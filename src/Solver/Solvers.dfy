module Solvers {
  export
    provides Solver, Solver.Extend, Solver.Prove, Solver.Record
    provides SolverExpr

  import opened SolverExpr

  datatype Solver =
    // TODO
    Solver(assumptions: seq<SExpr>)
  {
    method Extend(e: SExpr) returns (solver: Solver) {
      solver := Solver(assumptions + [e]);
    }
    method Prove(e: SExpr) {
      // TODO
      print "----- Proof obligation:\n";
      for i := 0 to |assumptions| {
        print "  ", assumptions[i], "\n";
      }
      print "  |-\n";
      print "  ", e, "\n";
    }
    method Record(e: SExpr) returns (solver: Solver)
    { solver := this; } // TODO
  }
}
