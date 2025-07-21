module Smt {
  // SMT command constants
  const CMD_PUSH: string := "(push)"
  const CMD_POP: string := "(pop)"
  const CMD_EXIT: string := "(exit)"
  const CMD_CHECK_SAT: string := "(check-sat)"
  const CMD_GET_MODEL: string := "(get-model)"

  // Opaque function to format assertion expressions
  opaque function AssertExpr(expr: string): string
    ensures AssertExpr(expr) != CMD_EXIT
    ensures AssertExpr(expr) != CMD_PUSH
    ensures AssertExpr(expr) != CMD_POP
  {
    "(assert " + expr + ")"
  }

  trait SmtProcess extends object {
    predicate Disposed()
      reads this

    method SendCmd(cmd: string) returns (response: string)
      requires !Disposed()
      modifies this
      ensures cmd == CMD_EXIT ==> Disposed()
      ensures cmd != CMD_EXIT ==> !Disposed()
  }

  // Trait for SMT solvers with incremental solving capabilities
  class Solver {
    const process: SmtProcess
    constructor(process: SmtProcess)
      requires !process.Disposed()
      ensures CommandStacks() == [[]]
      ensures !Disposed()
      ensures this.process == process
    {
      this.process := process;
      new;
      assume {:axiom} CommandStacks() == [[]];
    }

    // Ghost function to get the command stacks (axiomatized to ensure consistency)
    @Axiom
    ghost function CommandStacks(): seq<seq<string>>
      reads this.process

    predicate Disposed()
      reads this.process
    {
      this.process.Disposed()
    }

    ghost function PushCommandStack(commandStack: seq<seq<string>>): seq<seq<string>> {
      commandStack + [[]]  
    }
    ghost function PopCommandStack(commandStack: seq<seq<string>>): seq<seq<string>>
      requires 1 < |commandStack|
    {
      commandStack[..|commandStack|-1]
    }
    ghost function AddCommand(commandStack: seq<seq<string>>, cmd: string): seq<seq<string>> 
      requires 0 < |commandStack|
    {
      commandStack[..|commandStack|-1] +
        [commandStack[|commandStack|-1] + [cmd]]
    }
    // Send a command to the solver and get response
    method SendCmd(cmd: string) returns (response: string)
      requires !Disposed()
      requires |CommandStacks()| > 0
      modifies process // Hopefully one day we have private memory and we can say "modifies this"
      ensures cmd == CMD_EXIT <==> Disposed()
      ensures cmd == CMD_PUSH ==> CommandStacks() == PushCommandStack(old(CommandStacks()))
      ensures cmd == CMD_POP && |old(CommandStacks())| > 1 ==>
                CommandStacks() == PopCommandStack(old(CommandStacks()))
      ensures cmd != CMD_PUSH && cmd != CMD_POP ==>
                CommandStacks() == AddCommand(old(CommandStacks()), cmd)
    {
      response := process.SendCmd(cmd);

      assume {:axiom} cmd == CMD_PUSH ==> CommandStacks() == PushCommandStack(old(CommandStacks()));
      assume {:axiom} cmd == CMD_POP && |old(CommandStacks())| > 1 ==>
                CommandStacks() == PopCommandStack(old(CommandStacks()));
      assume {:axiom} cmd != CMD_PUSH && cmd != CMD_POP ==>
                CommandStacks() == AddCommand(old(CommandStacks()), cmd);
    }

    // Helper methods defined in terms of SendCmd
    method Push()
      requires !Disposed()
      requires |CommandStacks()| > 0
      modifies this, this.process
      ensures !Disposed()
      ensures CommandStacks() == old(CommandStacks()) + [[]]
    {
      var _ := SendCmd(CMD_PUSH);
      // The postcondition follows directly from SendCmd's postcondition
    }

    method Pop()
      requires !Disposed()
      requires |CommandStacks()| > 1 // There is always at least one command stack
      modifies this, this.process
      ensures !Disposed()
      ensures CommandStacks() == old(CommandStacks()[..|CommandStacks()|-1])
    {
      var _ := SendCmd(CMD_POP);
    }

    method Assert(expr: string)
      requires |CommandStacks()| > 0
      requires !Disposed()
      requires |CommandStacks()| > 0
      modifies this, this.process
      ensures !Disposed()
      ensures CommandStacks() == AddCommand(old(CommandStacks()), AssertExpr(expr))
    {
      var cmd := AssertExpr(expr);
      var _ := SendCmd(cmd);
    }

    method CheckSat() returns (result: string)
      requires |CommandStacks()| > 0
      requires !Disposed()
      modifies this, this.process
      ensures !Disposed()
      ensures CommandStacks() == AddCommand(old(CommandStacks()), CMD_CHECK_SAT)
    {
      result := SendCmd(CMD_CHECK_SAT);
    }

    method GetModel() returns (model: string)
      requires |CommandStacks()| > 0
      requires !Disposed()
      modifies this, this.process
      ensures !Disposed()
      ensures CommandStacks() == AddCommand(old(CommandStacks()), CMD_GET_MODEL)
    {
      model := SendCmd(CMD_GET_MODEL);
    }

    method Dispose()
      requires |CommandStacks()| > 0
      requires !Disposed()
      modifies this, this.process
      ensures Disposed()
    {
      var _ := SendCmd(CMD_EXIT);
      // The postcondition follows directly from SendCmd's postcondition
      assert Disposed();
    }
  }
}