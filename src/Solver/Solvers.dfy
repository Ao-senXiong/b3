module Solvers {
  export
    provides Solver, Solver.Extend, Solver.Prove, Solver.Record
    provides SolverExpr

  import opened SolverExpr

  datatype Solver = Solver()
  {
    method Extend(e: SExpr) returns (solver: Solver)
    method Prove(e: SExpr)
    method Record(e: SExpr) returns (solver: Solver)
  }
}
