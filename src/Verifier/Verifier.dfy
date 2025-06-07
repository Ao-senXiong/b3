module Verifier {
  import opened Basics
  import opened Ast
  import opened Solvers
  import opened SolverExpr

  newtype Incarnations = map<Variable, Var>
  {
    method New(v: Variable) returns (x: Var) {
      x := new Var(v.name);
    }
    function Eval(e: Expr): SExpr
    function DomainRestrict(s: set<Variable>): Incarnations {
      map v | v in this && v in s :: this[v]
    }
  }

  function IdExpr(v: Var): SExpr {
    CreateIdExpr(v)
  }

  // TODO: we should really start from a resolved AST
  function NameToResolvedVariable(name: string): Variable

  // map from block names to pairs (V, Ss) of variable sets and statement sequences
  type BlockContinuations = map<string, Continuation>
  datatype Continuation = Continuation(V: set<Variable>, continuation: seq<Stmt>)

  method Process(stmts: seq<Stmt>, incarnations: Incarnations, B: BlockContinuations, o: Solver)
    decreases |stmts|
  {
    if |stmts| == 0 {
      return;
    }

    var s0, cont := stmts[0], stmts[1..];
    match s0
    case VarDecl(v) =>
      var x := incarnations.New(v);
      Process(cont, incarnations[v := x], B, o);
    case ValDecl(v, rhs) =>
      var x := incarnations.New(v);
      Process(cont, incarnations[v := x], B, o);
    case Assign(lhs, rhs) =>
      var x := NameToResolvedVariable(lhs);
      var e' := incarnations.Eval(rhs);
      var x' := incarnations.New(x);
      var o' := o.Extend(CreateEq(IdExpr(x'), e'));
      Process(cont, incarnations[x := x'], B, o');
    case Block(lbl, stmts) =>
      var B' := B[lbl := Continuation(incarnations.Keys, cont)];
      Process(stmts + [Exit(lbl)], incarnations, B', o); // TODO: termination
    case Call(name, args) =>
      // TODO
    case Check(cond) =>
      // TODO
    case Assume(cond) =>
      // TODO
    case Assert(cond) =>
      // TODO
    case AForall(v, body) =>
      // TODO
    case If(cond, thn, els) =>
      var e' := incarnations.Eval(cond);
      var oThen := o.Extend(e');
      Process([thn] + cont, incarnations, B, oThen); // TODO: termination
      var oElse := o.Extend(CreateNegation(e'));
      Process([els] + cont, incarnations, B, oElse); // TODO: termination
    case IfCase(cases) =>
      for i := 0 to |cases| {
        var cs := cases[i];
        var e' := incarnations.Eval(cs.cond);
        var o' := o.Extend(e');
        Process([cs.body] + cont, incarnations, B, o'); // TODO: termination
      }
    case Loop(lbl, invariants, body) =>
      // TODO
    case Exit(lbl) =>
      expect lbl in B;
      var Continuation(V, cont') := B[lbl];
      var incarnations' := incarnations.DomainRestrict(V);
      Process(cont', incarnations', B, o); // TODO: termination
    case Return =>
      var lbl := ReturnLabel;
      expect lbl in B;
      var Continuation(V, cont') := B[lbl];
      var incarnations' := incarnations.DomainRestrict(V);
      Process(cont', incarnations', B, o); // TODO: termination
    case Probe(e) =>
      var e' := incarnations.Eval(e);
      var o' := o.Record(e');
      Process(cont, incarnations, B, o');
  }
}