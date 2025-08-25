module Smt {
  import opened Basics

  // SMT command constants
  const CMD_PUSH: string := "(push)"
  const CMD_POP: string := "(pop)"
  const CMD_EXIT: string := "(exit)"
  const CMD_CHECK_SAT: string := "(check-sat)"
  const CMD_GET_MODEL: string := "(get-model)"

  datatype Context =
    | Assumption(assumed: string)
    | Declaration(name: string, inputType: string, outputType: string)
  {
    function ToString(): (s: string)
      ensures s != CMD_EXIT
      ensures s != CMD_PUSH
      ensures s != CMD_POP
    {
      match this
      case Assumption(assumed) => "(assert " + assumed + ")"
      case Declaration(name, inputType, outputType) =>
        "(declare-fun " + name + " " + inputType + " " + outputType + ")"
    }
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

  // SMT engine (containing an SMT process) with incremental solving capabilities
  class SolverEngine {
    const process: SmtProcess
    constructor(process: SmtProcess)
      requires !process.Disposed()
      ensures CommandStacks() == Cons(Nil, Nil)
      ensures !Disposed()
      ensures this.process == process
    {
      this.process := process;
      new;
      assume {:axiom} CommandStacks() == Cons(Nil, Nil);
    }

    // Ghost function to get the command stacks (axiomatized to ensure consistency)
    @Axiom
    ghost function CommandStacks(): List<List<string>>
      reads this.process

    predicate Disposed()
      reads this.process
    {
      this.process.Disposed()
    }

    ghost function PushCommandStack(commandStack: List<List<string>>): List<List<string>> {
      Cons(Nil, commandStack)
    }
    ghost function PopCommandStack(commandStack: List<List<string>>): List<List<string>>
      requires commandStack.Cons?
    {
      commandStack.tail
    }
    ghost function AddCommand(commandStack: List<List<string>>, cmd: string): List<List<string>>
      requires commandStack.Cons?
    {
      commandStack.(head := Cons(cmd, commandStack.head))
    }
    // Send a command to the solver and get response
    method SendCmd(cmd: string) returns (response: string)
      requires !Disposed()
      requires CommandStacks().Cons?
      modifies process // Hopefully one day we have private memory and we can say "modifies this"
      ensures cmd == CMD_EXIT <==> Disposed()
      ensures cmd == CMD_PUSH ==> CommandStacks() == PushCommandStack(old(CommandStacks()))
      ensures old(allocated(CommandStacks()))
      ensures cmd == CMD_POP && old(CommandStacks().DoubleCons?) ==>
                CommandStacks() == PopCommandStack(old(CommandStacks()))
      ensures cmd != CMD_PUSH && cmd != CMD_POP ==>
                CommandStacks() == AddCommand(old(CommandStacks()), cmd)
    {
      // print ">> ", cmd, "\n"; // for debugging

      response := process.SendCmd(cmd);
      assume {:axiom} old(allocated(CommandStacks()));
      assume {:axiom} cmd == CMD_PUSH ==> CommandStacks() == PushCommandStack(old(CommandStacks()));
      assume {:axiom} cmd == CMD_POP && old(CommandStacks().DoubleCons?) ==>
          CommandStacks() == PopCommandStack(old(CommandStacks()));
      assume {:axiom} cmd != CMD_PUSH && cmd != CMD_POP ==>
          CommandStacks() == AddCommand(old(CommandStacks()), cmd);
    }

    ghost predicate Valid() reads this, this.process {
      && !Disposed()
      && CommandStacks().Cons?
    }

    // Helper methods defined in terms of SendCmd
    method Push()
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks() == PushCommandStack(old(CommandStacks()))
    {
      var _ := SendCmd(CMD_PUSH);
      // The postcondition follows directly from SendCmd's postcondition
    }

    method Pop()
      requires Valid()
      requires CommandStacks().DoubleCons? // There is always at least one command stack
      modifies this, this.process
      ensures Valid()
      ensures old(allocated(CommandStacks()))
      ensures CommandStacks() == old(CommandStacks().tail)
    {
      var _ := SendCmd(CMD_POP);
    }

    method DeclareFunction(
      name: string,
      inputTpe: string,
      outputTpe: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks()
           == AddCommand(old(CommandStacks()), Declaration(name, inputTpe, outputTpe).ToString())
    {
      var cmd := Declaration(name, inputTpe, outputTpe).ToString();
      var _ := SendCmd(cmd);
    }

    method Assume(expr: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks()
           == AddCommand(old(CommandStacks()), Assumption(expr).ToString())
    {
      var cmd := Assumption(expr).ToString();
      var _ := SendCmd(cmd);
    }

    method CheckSat() returns (result: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks() == AddCommand(old(CommandStacks()), CMD_CHECK_SAT)
    {
      result := SendCmd(CMD_CHECK_SAT);
    }

    method GetModel() returns (model: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks() == AddCommand(old(CommandStacks()), CMD_GET_MODEL)
    {
      model := SendCmd(CMD_GET_MODEL);
    }

    method Dispose()
      requires Valid()
      modifies this, this.process
      ensures Disposed()
    {
      var _ := SendCmd(CMD_EXIT);
      // The postcondition follows directly from SendCmd's postcondition
      assert Disposed();
    }
  }
}