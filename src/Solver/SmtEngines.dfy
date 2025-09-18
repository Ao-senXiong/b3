module SmtEngines {
  import opened Basics
  import opened Std.Wrappers
  import ExternalSolvers
  import OSProcesses

  export
    reveals SolverEngine
    provides SolverEngine.Valid, SolverEngine.process
    provides SolverEngine.Push, SolverEngine.Pop, SolverEngine.Assume
    provides SolverEngine.DeclareSort, SolverEngine.DeclareFunction, SolverEngine.CheckSat
    provides SolverEngine.GetModel, SolverEngine.Dispose
    provides SolverEngine.CommandStacks
    reveals SolverEngine.PushCommandStack, SolverEngine.PopCommandStack, SolverEngine.AddCommand
    reveals Context
    provides Context.ToString
    provides CMD_PUSH, CMD_POP, CMD_EXIT, CMD_CHECK_SAT, CMD_GET_MODEL
    provides OSProcesses, Wrappers, Basics

  // SMT command constants
  const CMD_PUSH: string := "(push)"
  const CMD_POP: string := "(pop)"
  const CMD_EXIT: string := "(exit)"
  const CMD_CHECK_SAT: string := "(check-sat)"
  const CMD_GET_MODEL: string := "(get-model)"

  datatype Context =
    | Assumption(assumed: string)
    | Declaration(name: string, inputType: string, outputType: string)
    | SortDeclaration(name: string)
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
      case SortDeclaration(name) =>
        "(declare-sort " + name + " 0)"
    }
  }

  // SMT engine (containing an OS process) with incremental solving capabilities
  class SolverEngine {
    const process: OSProcesses.OSProcess
    const printLog: bool

    // The following variable seeks to explain the state of the solver engine
    ghost var CommandStacks: List<List<string>>

    constructor (process: OSProcesses.OSProcess, printLog: bool)
      requires process.Valid()
      ensures Valid()
      ensures this.process == process
      ensures CommandStacks == Cons(Nil, Nil)
    {
      this.process := process;
      this.printLog := printLog;
      CommandStacks := PushCommandStack(Nil);
    }

    ghost static function PushCommandStack(commandStack: List<List<string>>): List<List<string>> {
      Cons(Nil, commandStack)
    }

    ghost static function PopCommandStack(commandStack: List<List<string>>): List<List<string>>
      requires commandStack.Cons?
    {
      commandStack.tail
    }

    ghost static function AddCommand(commandStack: List<List<string>>, cmd: string): List<List<string>>
      requires commandStack.Cons?
    {
      commandStack.(head := Cons(cmd, commandStack.head))
    }

    // Send a command to the solver and get response
    method SendCmd(cmd: string) returns (r: Result<string, string>)
      requires Valid()
      requires CommandStacks.Cons?
      modifies this, process
      ensures cmd != CMD_EXIT ==> Valid()
      ensures
        && (cmd == CMD_PUSH ==> CommandStacks == PushCommandStack(old(CommandStacks)))
        && (cmd == CMD_POP && old(CommandStacks.DoubleCons?) ==> CommandStacks == PopCommandStack(old(CommandStacks)))
        && (cmd != CMD_PUSH && cmd != CMD_POP ==> CommandStacks == AddCommand(old(CommandStacks), cmd))
    {
      if printLog {
        print "smt>> ", cmd, "\n";
      }

      if cmd == CMD_PUSH {
        CommandStacks := PushCommandStack(CommandStacks);
      } else if cmd == CMD_POP && CommandStacks.DoubleCons? {
        CommandStacks := PopCommandStack(CommandStacks);
      } else if cmd != CMD_PUSH && cmd != CMD_POP {
        CommandStacks := AddCommand(CommandStacks, cmd);
      }

      r := ExternalSolvers.Send(process, cmd);
    }

    ghost predicate Valid()
      reads this, this.process
    {
      && process.Valid()
      && CommandStacks.Cons?
    }

    method Push()
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == PushCommandStack(old(CommandStacks))
    {
      var _ := SendCmd(CMD_PUSH);
    }

    method Pop()
      requires Valid()
      requires CommandStacks.DoubleCons? // there is always at least one command stack
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == old(CommandStacks.tail)
    {
      var _ := SendCmd(CMD_POP);
    }

    method DeclareSort(name: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == AddCommand(old(CommandStacks), SortDeclaration(name).ToString())
    {
      var cmd := SortDeclaration(name).ToString();
      var _ := SendCmd(cmd);
    }

    method DeclareFunction(name: string, inputTypes: string, outputType: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == AddCommand(old(CommandStacks), Declaration(name, inputTypes, outputType).ToString())
    {
      var cmd := Declaration(name, inputTypes, outputType).ToString();
      var _ := SendCmd(cmd);
    }

    method Assume(expr: string)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == AddCommand(old(CommandStacks), Assumption(expr).ToString())
    {
      var cmd := Assumption(expr).ToString();
      var _ := SendCmd(cmd);
    }

    method CheckSat() returns (r: Result<string, string>)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == AddCommand(old(CommandStacks), CMD_CHECK_SAT)
    {
      r := SendCmd(CMD_CHECK_SAT);
    }

    method GetModel() returns (r: Result<string, string>)
      requires Valid()
      modifies this, this.process
      ensures Valid()
      ensures CommandStacks == AddCommand(old(CommandStacks), CMD_GET_MODEL)
    {
      r := SendCmd(CMD_GET_MODEL);
    }

    method Dispose()
      requires Valid()
      modifies this, this.process
    {
      var _ := SendCmd(CMD_EXIT);
    }
  }
}