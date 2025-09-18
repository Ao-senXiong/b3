module ExternalSolvers {
  import opened Basics
  import opened Std.Wrappers
  import opened OSProcesses

  export
    reveals SolverSelection
    provides StartSmtSolverProcess, Send
    provides Wrappers, OSProcesses

  datatype SolverSelection = Z3 | CVC5

  method StartSmtSolverProcess(which: SolverSelection) returns (r: Result<OSProcess, string>)
    ensures r.Success? ==> var process := r.value; process.Valid() && fresh(process)
  {
    var process;
    match which {
      case Z3 =>
        process :- OSProcess.Create("z3", "-in");
      case CVC5 =>
        process :- OSProcess.Create("cvc5", "--incremental");
    }

    // Initialize SMT solver with some SMT-LIB2 commands
    var _ :- Send(process, "(set-option :produce-models true)");
    var _ :- Send(process, "(set-logic ALL)");

    return Success(process);
  }

  method Send(p: OSProcess, cmd: string) returns (r: Result<string, string>)
    requires p.Valid()
    modifies p
    ensures r.Success? && cmd != "(exit)" ==> p.Valid()
  {
    Log(p, ToProcess, cmd);

    var _ := p.Send(cmd);

    // For simple commands like (push), (pop), there is no response from the SMT solver
    if
      || cmd == "(push)"
      || cmd == "(pop)"
      || "(assert " <= cmd
      || "(set-option " <= cmd
      || "(set-logic " <= cmd
      || "(declare-fun " <= cmd
      || "(declare-const " <= cmd
      || "(declare-sort " <= cmd
      || cmd == "(exit)"
    {
      return Success("");
    }

    // For get-model, read until we get a balanced set of parentheses
    if cmd == "(get-model)" {
      r := ReadBalancedParentheses(p);
      return;
    }

    // In all other cases, including the command check-sat, the response is a single line
    var line :- p.ReadLine();
    match line
    case None => return Success("");
    case Some(text) => return Success(text);
  }

  method ReadBalancedParentheses(p: OSProcess) returns (r: Result<string, string>)
    requires p.Valid()
    modifies p
    ensures r.Success? ==> p.Valid()
  {
    // Read until we get a balanced set of parentheses
    var response := "";
    var parenCount: nat := 0;
    var started := false;
    // We don't actually know that the process is going to give us a finite amount
    // of response output. However, we will in effect assume that here, by dreaming
    // up the number of characters we're expecting in the reponse.
    ghost var lengthOfEntireResponse :| 0 <= lengthOfEntireResponse;
    assert |response| == 0 <= lengthOfEntireResponse;
    while true
      invariant |response| <= lengthOfEntireResponse
      decreases lengthOfEntireResponse - |response|
    {
      var line :- p.ReadLine();
      match line
      case None =>
        // at end of file; okay, so this is unexpected, but let's just return what we've got so far
        return Success(response);
      case Some(text) =>
        response := response + text + "\n";

        for i := 0 to |text| {
          var ch := text[i];
          if ch == '(' {
            started := true;
            parenCount := parenCount + 1;
          } else if ch == ')' {
            if !started || parenCount == 0 {
              // malformed parentheses; just return what we've got so far
              return Success(response);
            }
            parenCount := parenCount - 1;
          }
        }

        if started && parenCount == 0 {
          // perfect
          return Success(response);
        }
        assume {:axiom} |response| <= lengthOfEntireResponse;
    }
  }

  const DEBUG: bool := false

  datatype Direction = ToProcess | FromProcess

  method Log(p: OSProcess, direction: Direction, msg: string) {
    if DEBUG {
      print p.ExecutableName();
      match direction {
        case ToProcess => print " << ";
        case FromProcess => print " >> ";
      }
      print msg, "\n";
    }
  }
}