/// Module RSolver provides three types:
///   * REXpr - an AST for the solver's expressions
///   * RContext - a conjunction of assumptions, represented as a node in a tree
///   * REngine - an SMT-backed engine that can answer proof queries in a given context
module RSolvers {
  import SolverExpr
  import Solvers
  import Z3SmtSolver
  import opened Std.Wrappers
  import opened Basics

  export
    reveals RExpr
    provides RExpr.Eq
    provides RContext, CreateEmptyContext, Extend, Record
    reveals REngine
    provides CreateEngine, REngine.Repr, REngine.Valid, REngine.Prove
    provides SolverExpr

  // ===== RExpr =====

  datatype RExpr =
    | Boolean(b: bool)
    | Integer(x: int)
    | Id(v: SolverExpr.SVar)
    | FuncAppl(op: string, args: seq<RExpr>)
  {
    function ToSExpr(): SolverExpr.SExpr {
      match this
      case Boolean(b) => SolverExpr.SExpr.Boolean(b)
      case Integer(x) => SolverExpr.SExpr.Integer(x)
      case Id(v) => SolverExpr.SExpr.Id(v)
      case FuncAppl(op, args) =>
        var sargs := SeqMap(args, (arg: RExpr) requires arg < this => arg.ToSExpr());
        SolverExpr.SExpr.FuncAppl(op, sargs)
    }

    static function Eq(r0: RExpr, r1: RExpr): RExpr {
      FuncAppl("=", [r0, r1])
    }

    function ToString(): string {
      match this
      case Boolean(b) => if b then "true" else "false"
      case Integer(x) => Int2String(x)
      case Id(v) => v.name
      case FuncAppl(op, args) =>
        var argStrings := SeqMap(args, (arg: RExpr) requires arg < this => arg.ToString());
        op + "(" + Comma(argStrings, ", ") + ")"
    }
  }

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

    method Prove(context: RContext, expr: RExpr)
      requires Valid()
      modifies Repr
      ensures Valid()
    {
      PrintProofObligation(context, expr);
      SetContext(context);

      state.Push(context); // do another Push; the parameter here is irrelevant and will soon be popped off again
      DeclareNewSymbols(expr);
      var result := state.Prove(expr.ToSExpr());
      state.Pop();

      // TODO: do something with `result` (other than just printing it)
      print "Result:", result, "\n";
    }

    method SetContext(context: RContext)
      requires Valid()
      modifies Repr
      ensures Valid()
    {
      var memoCount := state.memos.Length();
      // First, trim down memo length to be no greater than the context depth
      while context.depth < memoCount
        invariant Valid() && memoCount == state.memos.Length()
        decreases memoCount
      {
        state.Pop();
        memoCount := memoCount - 1;
      }

      AdjustContext(context);
    }

    method AdjustContext(context: RContext)
      requires Valid() && state.memos.Length() <= context.depth
      modifies Repr
      ensures Valid() && (state.memos.Length() == context.depth == 0 || state.IsTopMemo(context))
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
      if state.memos.Length() < contextx.depth {
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

    method DeclareNewSymbols(r: RExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && state.memos == old(state.memos)
    {
      match r
      case Boolean(_) =>
      case Integer(_) =>
      case Id(v) =>
        if v !in state.declarations {
          state.DeclareSymbol(v);
        }
      case FuncAppl(op, args) =>
        for i := 0 to |args|
          invariant Valid() && state.memos == old(state.memos)
        {
          DeclareNewSymbols(args[i]);
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


















/*************************
  method Create() returns (r: RSolver)
    ensures r.Valid() && fresh(r.Repr)
  {
    var smtEngine := Z3SmtSolver.CreateZ3SolverEngine();
    var state := new Solvers.SolverState(smtEngine);
    var solver := Solvers.Solver.Empty();
    return RSolver(solver, state, 0, None);
  }

  datatype RSolver = RSolver(solver: Solvers.Solver, state: Solvers.SolverState, depth: nat, previous: Option<RSolver>)
  {
    ghost const Repr: set<object> := { state, state.smtEngine, state.smtEngine.process }

    ghost predicate Valid()
      reads Repr
    {
      state.Valid() &&
      state.ValidFor(solver) &&
      match previous
      case None => depth == 0
      case Some(prev) =>
        prev.state == state && prev.depth < depth
    }

    method Extend(expr: RExpr) returns (r: RSolver)
      requires Valid()
      modifies Repr
      ensures r.Valid() && fresh(r.Repr - Repr)
    {
      var solver := this.solver;
      // TODO: declare the new symbols in "expr"
      solver := solver.Extend(expr.ToSExpr(), state);
      r := RSolver(solver, state, depth + 1, Some(this));
    }

    method Prove(expr: RExpr)
      requires Valid()
      modifies Repr
      ensures Valid()
    {
      // TODO: declare the new symbols in "expr"
      solver.Prove(expr.ToSExpr(), state);
    }

    method Record(expr: RExpr) returns (r: RSolver)
      requires Valid()
      modifies Repr
      ensures r.Valid() && fresh(r.Repr - Repr)
    {
      // TODO: declare the new symbols in "expr"
      var solver := solver.Record(expr.ToSExpr());
      return RSolver(solver, state, depth + 1, Some(this));
    }
  }
*************************/
}