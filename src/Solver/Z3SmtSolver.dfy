module Z3SmtSolver {
  import opened Smt

  @Test
  method DemonstrateZ3() {
    // Create Z3 solver
    var z3 := CreateZ3SolverEngine();
    

    z3.DeclareFunction("x", "()", "Int");

    z3.Push();
    
    // Example: Check if x > y and y > x is satisfiable
    z3.DeclareFunction("y", "()", "Int");

    // Assert x > y
    z3.Assume("(> x y)");
    
    // Assert y > x
    z3.Assume("(> y x)");
    
    // Check satisfiability
    var result := z3.CheckSat();
    
    // Print result (should be "unsat")
    print "Checking if x > y and y > x is satisfiable: ", result, "\n";
    expect result == "unsat";
    
    // Pop back to clean state
    z3.Pop();
    
    // Example: Check if x >= 0 and x <= 10 is satisfiable
    z3.Push();
    
    // Assert x >= 0
    z3.Assume("(>= x 0)");
    
    // Assert x <= 10
    z3.Assume("(<= x 10)");
    
    // Check satisfiability
    result := z3.CheckSat();
    
    // Print result (should be "sat")
    print "Checking if x >= 0 and x <= 10 is satisfiable: ", result, "\n";
    expect result == "sat";
    
    // If satisfiable, get a model
    var model := z3.GetModel();
    print "Model: ", model, "\n";
    
    // Pop back to clean state
    z3.Pop();
    
    // Clean up
    z3.Dispose();
  }

  // Factory method to create a Z3 solver instance
  @Axiom
  method {:extern} CreateZ3Process() returns (process: Smt.SmtProcess)
    ensures !process.Disposed()
    ensures fresh(process)
  
  method CreateZ3SolverEngine() returns (smtEngine: SolverEngine)
    ensures !smtEngine.Disposed()
    ensures smtEngine.CommandStacks() == Basics.Cons(Basics.Nil, Basics.Nil)
    ensures fresh(smtEngine) && fresh(smtEngine.process)
  {
    var process := CreateZ3Process();
    smtEngine := new SolverEngine(process);
  }
}