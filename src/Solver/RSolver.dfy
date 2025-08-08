/// Module RSolver provides three types:
///   * REXpr - an AST for the solver's expressions
///   * RContext - a conjunction of assumptions, represented as a node in a tree
///   * REngine - an SMT-backed engine that can answer proof queries in a given context
module RSolvers {
  import SolverExpr
  import Solvers
  import Z3SmtSolver
  import opened Std.Wrappers

  export
    reveals RExpr
    provides RExpr.Eq
    provides RContext, CreateEmptyContext
    reveals REngine
    provides CreateEngine, REngine.Repr, REngine.Valid, REngine.Prove
    // ...
    provides RSolver, RSolver.Repr, RSolver.Valid
    provides Create
    provides RSolver.Extend, RSolver.Prove, RSolver.Record
    provides SolverExpr, Solvers

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
      case FuncAppl(op, args) => SolverExpr.SExpr.FuncAppl(op, seq(|args|, i requires 0 <= i < |args| => args[i].ToSExpr()))
    }

    static function Eq(r0: RExpr, r1: RExpr): RExpr {
      FuncAppl("=", [r0, r1])
    }
  }

  // ===== RContext =====

  trait RContext_ extends object {
    const depth: nat
    ghost predicate Valid()
  }

  class RContextRoot extends RContext_ {
    ghost predicate Valid() {
      depth == 0
    }

    constructor ()
      ensures Valid()
    {
      depth := 0;
    }
  }

  class RContextNode extends RContext_ {
    const parent: RContext
    const expr: RExpr

    ghost predicate Valid() {
      depth == parent.depth + 1
    }

    constructor (parent: RContext, expr: RExpr)
      ensures Valid()
    {
      this.depth := parent.depth + 1;
      this.parent := parent;
      this.expr := expr;
    }
  }

  type RContext = r: RContext_ | r.Valid() witness *

  method CreateEmptyContext() returns (context: RContext) {
    context := new RContextRoot();
  }
  
  method Extend(context: RContext, expr: RExpr) returns (r: RContext) {
    r := new RContextNode(context, expr);
  }

  // ===== REngine =====

  class REngine {
    const Repr: set<object>
    ghost predicate Valid()
      reads Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr
    }

    // This constructor is given a name, so that it doesn't automatically get exported just because the class is revealed
    constructor New(state: Solvers.SolverState)
      ensures Valid() && fresh(Repr)
    {
      Repr := {this};
    }

    method Prove(context: RContext, expr: RExpr)
  }

  method CreateEngine() returns (r: REngine)
    ensures r.Valid() && fresh(r.Repr)
  {
    var z3 := Z3SmtSolver.CreateZ3SolverEngine();
    var state := new Solvers.SolverState(z3);
    r := new REngine.New(state);
  }



















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
}