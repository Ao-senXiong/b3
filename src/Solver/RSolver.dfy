/// Module RSolver provides three types:
///   * REXpr - an AST for the solver's expressions
///   * RContext - a conjunction of assumptions, represented as a node in a tree
///   * REngine - an SMT-backed engine that can answer proof queries in a given context
module RSolvers {
  import SolverExpr
  import Solvers
  import Z3SmtSolver
  import Ast
  import opened Std.Wrappers
  import opened Basics

  export
    reveals RExpr, ROperator, RPattern
    provides RExpr.Eq, RExpr.Operator2ROperator, RExpr.OperatorToString
    provides RContext, CreateEmptyContext, Extend, Record
    reveals REngine
    provides CreateEngine, REngine.Repr, REngine.Valid, REngine.Prove
    provides SolverExpr, Solvers, Ast

  // ===== RExpr =====

  type SExpr = SolverExpr.SExpr

  datatype ROperator = BuiltInOperator(name: string) | UserDefinedFunction(decl: SolverExpr.SDeclaration)
  {
    function ToString(): string {
      match this
      case BuiltInOperator(name) => name
      case UserDefinedFunction(decl) => decl.name
    }
  }

  datatype RExpr =
    | Boolean(b: bool)
    | Integer(x: int)
    | CustomLiteral(s: string, typ: SolverExpr.SType)
    | Id(v: SolverExpr.SVar)
    | FuncAppl(op: ROperator, args: seq<RExpr>)
    | IfThenElse(guard: RExpr, thn: RExpr, els: RExpr)
    | LetExpr(v: SolverExpr.SVar, rhs: RExpr, body: RExpr)
    | QuantifierExpr(univ: bool, v: SolverExpr.SVar, patterns: seq<RPattern>, body: RExpr)
  {
    function ToSExpr(): SExpr {
      match this
      case Boolean(b) => SExpr.Boolean(b)
      case Integer(x) => SExpr.Integer(x)
      case CustomLiteral(s, _) => SExpr.S("|" + s + "|")
      case Id(v) => SExpr.Id(v)
      case FuncAppl(op, args) =>
        var sargs := RExprListToSExprs(args, this);
        SExpr.FuncAppl(op.ToString(), sargs)
      case IfThenElse(guard, thn, els) =>
        SExpr.FuncAppl("ite", [guard.ToSExpr(), thn.ToSExpr(), els.ToSExpr()])
      case LetExpr(v, rhs, body) =>
        var binding := SExpr.PP([SExpr.Id(v), rhs.ToSExpr()]);
        SExpr.FuncAppl("let", [SExpr.PP([binding]), body.ToSExpr()])
      case QuantifierExpr(univ, v, patterns, body) =>
        var boundVar := SExpr.PP([SExpr.Id(v), v.typ.ToSExpr()]); // "(x Int)"
        var sbody :=
          if patterns == [] then
            body.ToSExpr()
          else
            SExpr.FuncAppl("!", [body.ToSExpr()] + PatternListToSExprs(patterns, this)); // "(! body :pattern (t0 t1 t2) :pattern (u0 u1))"
        SExpr.FuncAppl(if univ then "forall" else "exists", [SExpr.PP([boundVar]), sbody])
    }

    static function RExprListToSExprs(exprs: seq<RExpr>, ghost parent: RExpr): seq<SExpr>
      requires forall expr <- exprs :: expr < parent
      decreases parent, 0, |exprs|
    {
      SeqMap(exprs, (expr: RExpr) requires expr < parent => expr.ToSExpr())
    }

    static function PatternListToSExprs(patterns: seq<RPattern>, ghost parent: RExpr): seq<SExpr>
      requires forall tr <- patterns :: tr < parent
      decreases parent, |patterns|
    {
      if patterns == [] then
        []
      else
        var pattern := patterns[0];
        assert pattern in patterns;
        var terms := RExprListToSExprs(pattern.exprs, parent);
        assert forall tr <- patterns[1..] :: tr in patterns;
        [SExpr.S(":pattern"), SExpr.PP(terms)] + PatternListToSExprs(patterns[1..], parent)
    }

    static function Operator2ROperator(op: Ast.Operator): ROperator
      requires op != Ast.Operator.IfThenElse && op != Ast.Operator.Neq
    {
      BuiltInOperator(OperatorToString(op))
    }

    static function OperatorToString(op: Ast.Operator): string
      requires op != Ast.Operator.IfThenElse && op != Ast.Operator.Neq
    {
      match op
      case Equiv => "-"
      case LogicalImp => "=>"
      case LogicalAnd => "and"
      case LogicalOr => "or"
      case Eq => "="
      case Less => "<"
      case AtMost => "<="
      case Plus => "+"
      case Minus => "-"
      case Times => "*"
      case Div => "/"
      case Mod => "%"
      case LogicalNot => "not"
      case UnaryMinus => "-"
    }

    static function Eq(r0: RExpr, r1: RExpr): RExpr {
      FuncAppl(BuiltInOperator(SExpr.EQ), [r0, r1])
    }

    // Convert the RExpr to a B3-like expression
    function ToString(): string {
      match this
      case Boolean(b) => if b then "true" else "false"
      case Integer(x) => Int2String(x)
      case CustomLiteral(s, typ) => Ast.CustomLiteralToString(s, typ.ToString())
      case Id(v) => v.name
      case FuncAppl(op, args) =>
        op.ToString() + "(" + RExprListToString(args, this) + ")"
      case IfThenElse(guard, thn, els) =>
        "(if " + guard.ToString() + " then " + thn.ToString() + " else " + els.ToString() + ")"
      case LetExpr(v, rhs, body) =>
        "(val " + v.name + ": " + v.typ.ToString() + " := " + rhs.ToString() + " " + body.ToString() + ")"
      case QuantifierExpr(univ, v, patterns, body) =>
        (if univ then "(forall " else "(exists ") +
        v.name + ": " + v.typ.ToString() +
        PatternsToString(patterns, this) +
        " :: " + body.ToString() + ")"
    }

    static function RExprListToString(exprs: seq<RExpr>, ghost parent: RExpr): string
      requires forall expr <- exprs :: expr < parent
      decreases parent, 0, |exprs|
    {
      var exprStrings := SeqMap(exprs, (expr: RExpr) requires expr < parent => expr.ToString());
      Comma(exprStrings, ", ")
    }

    static function PatternsToString(patterns: seq<RPattern>, ghost parent: RExpr): string
      requires forall tr <- patterns :: tr < parent
      decreases parent, |patterns|
    {
      if patterns == [] then
        ""
      else
        var pattern := patterns[0];
        assert pattern in patterns;
        assert forall tr <- patterns[1..] :: tr in patterns;
        " pattern " + RExprListToString(pattern.exprs, parent) + PatternsToString(patterns[1..], parent)
    }
  }

  datatype RPattern = RPattern(exprs: seq<RExpr>)

  // ===== RContext =====

  trait RContext_ extends object {
    const depth: nat
    ghost predicate Valid()
      decreases depth

    lemma JustTwoSubtypes()
      ensures this is RContextRoot || this is RContextNode

    method Print()
      requires Valid()
      decreases depth
  }

  class RContextRoot extends RContext_ {
    ghost predicate Valid()
      decreases depth
    {
      depth == 0
    }

    constructor ()
      ensures Valid()
    {
      depth := 0;
    }

    method Print()
      requires Valid()
      decreases depth
    {
    }

    lemma JustTwoSubtypes()
      ensures this is RContextRoot
    {
    }
  }

  class RContextNode extends RContext_ {
    const parent: RContext_
    const expr: RExpr

    ghost predicate Valid()
      decreases depth
    {
      depth == parent.depth + 1 &&
      parent.Valid()
    }

    constructor (parent: RContext, expr: RExpr)
      ensures Valid()
    {
      this.depth := parent.depth + 1;
      this.parent := parent;
      this.expr := expr;
    }

    method Print()
      requires Valid()
      decreases depth
    {
      parent.Print();
      print "  ", expr.ToString(), "\n";
    }

    lemma JustTwoSubtypes()
      ensures this is RContextNode
    {
    }
  }

  type RContext = r: RContext_ | r.Valid() witness *

  method PrintProofObligation(context: RContext, expr: RExpr) {
    print "----- Proof obligation:\n";
    context.Print();
    print "  |-\n";
    print "  ", expr.ToString(), "\n";
  }

  method CreateEmptyContext() returns (context: RContext) {
    context := new RContextRoot();
  }
  
  method Extend(context: RContext, expr: RExpr) returns (r: RContext) {
    r := new RContextNode(context, expr);
  }

  method Record(context: RContext, expr: RExpr) returns (r: RContext) {
    var name := "probe%" + Int2String(context.depth);
    var p := new SolverExpr.SVar(name, SolverExpr.SBool); // TODO: use the type of `expr`
    var eq := RExpr.Eq(RExpr.Id(p), expr);
    r := Extend(context, eq);
  }

  // ===== REngine =====

  class REngine {
    ghost const Repr: set<object>
    const state: Solvers.SolverState<RContext>

    ghost predicate Valid()
      reads Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && state in Repr && state.Repr <= Repr && this !in state.Repr
      && state.Valid()
    }

    // This constructor is given a name, so that it doesn't automatically get exported just because the class is revealed
    constructor New(state: Solvers.SolverState<RContext>)
      requires state.Valid()
      ensures Valid() && fresh(Repr - state.Repr)
    {
      this.state := state;
      Repr := {this} + state.Repr;
    }

    method Prove(context: RContext, expr: RExpr) returns (result: Solvers.ProofResult)
      requires Valid()
      modifies Repr
      ensures Valid()
    {
      PrintProofObligation(context, expr);
      SetContext(context);

      state.Push(context); // do another Push; the parameter here is irrelevant and will soon be popped off again
      DeclareNewSymbols(expr);
      result := state.Prove(expr.ToSExpr());
      state.Pop();
    }

    method SetContext(context: RContext)
      requires Valid()
      modifies Repr
      ensures Valid()
    {
      var memoCount := state.stack.Length();
      // First, trim down memo length to be no greater than the context depth
      while context.depth < memoCount
        invariant Valid() && memoCount == state.stack.Length()
        decreases memoCount
      {
        state.Pop();
        memoCount := memoCount - 1;
      }

      AdjustContext(context);
    }

    method AdjustContext(context: RContext)
      requires Valid() && state.stack.Length() <= context.depth
      modifies Repr
      ensures Valid() && (state.stack.Length() == context.depth == 0 || state.IsTopMemo(context))
      decreases context.depth
    {
      if context.depth == 0 {
        // done
        return;
      }

      var contextx := context as RContextNode by {
        var bug := contextx; // BUG: This Dafny scoping rule is wrong. It should not include the newly declared variables
        assert context is RContextNode by {
          context.JustTwoSubtypes();
          if context is RContextRoot {
            // proof by contradiction
            assert (context as RContextRoot).depth == 0;
          }
        }
      }
      if state.stack.Length() < contextx.depth {
        AdjustContext(contextx.parent);
      } else if state.IsTopMemo(contextx) {
        return;
      } else {
        state.Pop();
        AdjustContext(contextx.parent);
      }
      state.Push(contextx);
      DeclareNewSymbols(contextx.expr);
      state.AddAssumption(contextx.expr.ToSExpr());
    }

    method DeclareNewSymbols(r: RExpr, exclude: set<SolverExpr.SVar> := {})
      requires Valid()
      modifies Repr
      ensures Valid() && state.stack == old(state.stack)
    {
      match r
      case Boolean(_) =>
      case Integer(_) =>
      case CustomLiteral(_, _) =>
      case Id(v) =>
        if v !in exclude && v !in state.declarations {
          DeclareNewTypes(v.typ);
          state.DeclareSymbol(v);
        }
      case FuncAppl(op, args) =>
        // TODO: declare the function itself, unless it's a built-in SMT function (like `+`)
        for i := 0 to |args|
          invariant Valid() && state.stack == old(state.stack)
        {
          DeclareNewSymbols(args[i], exclude);
        }
      case IfThenElse(guard, thn, els) =>
        DeclareNewSymbols(guard, exclude);
        DeclareNewSymbols(thn, exclude);
        DeclareNewSymbols(els, exclude);
      case LetExpr(v, rhs, body) =>
        DeclareNewSymbols(rhs, exclude);
        DeclareNewSymbols(body, exclude + {v});
      case QuantifierExpr(_, v, patterns, body) =>
        var exclude' := exclude + {v};
        for i := 0 to |patterns|
          invariant Valid() && state.stack == old(state.stack)
        {
          var tr := patterns[i];
          for j := 0 to |tr.exprs|
            invariant Valid() && state.stack == old(state.stack)
          {
            DeclareNewSymbols(tr.exprs[j], exclude');
          }
        }
        DeclareNewSymbols(body, exclude');
    }

    method DeclareNewTypes(typ: SolverExpr.SType)
      requires Valid()
      modifies Repr
      ensures Valid() && state.stack == old(state.stack)
    {
      match typ
      case SBool | SInt =>
      case SUserType(decl) =>
        if decl !in state.declarations {
          state.DeclareType(decl);
        }
    }
  }

  method CreateEngine() returns (r: REngine)
    ensures r.Valid() && fresh(r.Repr)
  {
    var z3 := Z3SmtSolver.CreateZ3SolverEngine();
    var state := new Solvers.SolverState(z3);
    r := new REngine.New(state);
  }
}
