module RSolvers {
  import SolverExpr
  import Solvers
  import Z3SmtSolver

  export
    provides RSolver, RSolver.Repr, RSolver.Valid
    provides Create
    provides RSolver.Extend, RSolver.Prove, RSolver.Record
    reveals RExpr
    provides RExpr.Eq
    provides SolverExpr, Solvers

  method Create() returns (r: RSolver)
    ensures r.Valid() && fresh(r.Repr())
  {
    var z3 := Z3SmtSolver.CreateZ3Solver();
    var state := new Solvers.SolverState(z3);
    var solver := Solvers.Solver.Empty();
    return RSolver(solver, state);
  }

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
      case FuncAppl(op, args) => SolverExpr.SExpr.FuncAppl(op, seq(|args|, i requires 0 <= i < |args| => args[i].ToSExpr()))
    }

    static function Eq(r0: RExpr, r1: RExpr): RExpr {
      FuncAppl("=", [r0, r1])
    }
  }

  datatype RSolver = RSolver(solver: Solvers.Solver, state: Solvers.SolverState)
  {
    function Repr(): set<object> {
      { state, state.solver, state.solver.process }
    }

    ghost predicate Valid()
      reads Repr()
    {
      state.Valid() && state.ValidFor(solver)
    }

    method Extend(expr: RExpr) returns (r: RSolver)
      requires Valid()
      modifies Repr()
      ensures r.Valid() && r.Repr() == Repr()
    {
      var solver := this.solver;
      // TODO: declare the new symbols in "expr"
      solver := solver.Extend(expr.ToSExpr(), state);
      return RSolver(solver, state);
    }

    method Prove(expr: RExpr)
      requires Valid()
      modifies Repr()
      ensures Valid()
    {
      // TODO: declare the new symbols in "expr"
      solver.Prove(expr.ToSExpr(), state);
    }

    method Record(expr: RExpr) returns (r: RSolver)
      requires Valid()
      modifies Repr()
      ensures r.Valid() && r.Repr() == Repr()
    {
      // TODO: declare the new symbols in "expr"
      var solver := solver.Record(expr.ToSExpr());
      return RSolver(solver, state);
    }
  }
}