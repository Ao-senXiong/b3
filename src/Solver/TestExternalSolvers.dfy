module TestExternalSolvers {
  import opened Std.Wrappers
  import ES = ExternalSolvers
  import OSProcesses
  import Smt = SmtEngines

  export // this test-harness module doesn't export anything

  @Test
  method DemonstrateExternalSolvers() {
    var r: Result<OSProcesses.OSProcess, string> := ES.StartSmtSolverProcess(ES.Z3);
    if r.Failure? {
      print "Error creating z3 process: ", r.error, "\n";
      return;
    }
    Demonstrate(r.value);

    r := ES.StartSmtSolverProcess(ES.CVC5);
    if r.Failure? {
      print "Error creating cvc5 process: ", r.error, "\n";
      return;
    }
    Demonstrate(r.value);
  }

  method Demonstrate(process: OSProcesses.OSProcess)
    requires process.Valid()
    modifies process
  {
    var smtEngine := new Smt.SolverEngine(process, false);

    smtEngine.DeclareFunction("x", "()", "Int");

    smtEngine.Push();
    
    // Example: Check if x > y and y > x is satisfiable
    smtEngine.DeclareFunction("y", "()", "Int");

    // Assert x > y
    smtEngine.Assume("(> x y)");
    
    // Assert y > x
    smtEngine.Assume("(> y x)");
    
    // Check satisfiability
    var result :- expect smtEngine.CheckSat();
    
    // Print result (should be "unsat")
    print "Checking if x > y and y > x is satisfiable: ", result, "\n";
    expect result == "unsat";
    
    // Pop back to clean state
    smtEngine.Pop();
    
    // Example: Check if x >= 0 and x <= 10 is satisfiable
    smtEngine.Push();
    
    // Assert x >= 0
    smtEngine.Assume("(>= x 0)");
    
    // Assert x <= 10
    smtEngine.Assume("(<= x 10)");
    
    // Check satisfiability
    result :- expect smtEngine.CheckSat();
    
    // Print result (should be "sat")
    print "Checking if x >= 0 and x <= 10 is satisfiable: ", result, "\n";
    expect result == "sat";
    
    // If satisfiable, get a model
    var model :- expect smtEngine.GetModel();
    print "Model: ", model, "\n";
    
    // Pop back to clean state
    smtEngine.Pop();
    
    // Clean up
    smtEngine.Dispose();
  }
}