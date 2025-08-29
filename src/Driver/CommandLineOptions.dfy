module CommandLineOptions {
  import opened Std.Wrappers
  import opened Basics

  export
    reveals Syntax, OptionInfo, CliResult
    provides Syntax.ToolName, Syntax.GetVerbs, Syntax.GetOptionInfo
    provides Parse
    provides Wrappers

  trait {:termination false} Syntax<Verb> {
    const ToolName: string

    method GetVerbs() returns (verbs: seq<(string, Verb)>)

    function GetOptionInfo(name: string): OptionInfo
  }

  datatype OptionInfo =
    | Unknown
    | ArgumentCount(n: nat)

  datatype CliResult<Verb> = CliResult(verb: Verb, options: map<string, seq<string>>, files: seq<string>)

  method Parse<Verb>(syntax: Syntax<Verb>, args: seq<string>) returns (result: Result<CliResult, string>) {
    if |args| < 2 {
      return Failure("Usage: " + syntax.ToolName + " <verb> <options> <filenames>");
    }

    var verbs := syntax.GetVerbs();
    var verb;
    if i :| 0 <= i < |verbs| && verbs[i].0 == args[1] {
      verb := verbs[i].1;
    } else {
      return Failure("Unrecognized verb: " + args[1]);
    }

    var options := map[];
    var files := [];
    var i := 2;
    while i < |args| {
      var arg := args[i];
      if "--" <= arg {
        var optionName := arg[2..];
        var info := syntax.GetOptionInfo(optionName);
        if info == Unknown {
          return Failure("Unknown option: --" + optionName);
        } else if |args| < i + 1 + info.n {
          return Failure("Option --" + optionName + " requires " + Int2String(info.n) + " arguments, but only " + Int2String(|args| - 1) + " are given");
        } else if optionName in options {
          return Failure("Option --" + optionName + " is given more than once");
        }
        options := options[optionName := args[i..i + info.n]];
        i := i + 1 + info.n;
      } else {
        files := files + [arg];
        i := i + 1;
      }
    }

    return Success(CliResult(verb, options, files));
  }
}