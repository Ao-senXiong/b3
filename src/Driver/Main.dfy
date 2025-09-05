module B3 {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import RawAst
  import Parser
  import Std.FileIO
  import SB = Std.Parsers.StringBuilders
  import Printer
  import Ast
  import Resolver
  import ResolvedPrinter
  import TypeChecker
  import StaticConsistency
  import Verifier
  import CLI = CommandLineOptions

  class B3CliSyntax extends CLI.Syntax<Verb> {
    constructor () {
      ToolName := "b3";
    }

    method GetVerbs() returns (verbs: seq<(string, Verb)>) {
      verbs := [
        ("parse", Parse),
        ("resolve", Resolve),
        ("verify", Verify)
      ];
    }

    function GetOptionInfo(name: string): CLI.OptionInfo {
      match name
      case "print" => CLI.OptionInfo.ArgumentCount(0)
      case "rprint" => CLI.OptionInfo.ArgumentCount(0)
      case "solver-log" => CLI.OptionInfo.ArgumentCount(0)
      case _ => CLI.OptionInfo.Unknown
    }
  }

  datatype Verb = Parse | Resolve | Verify

  method Main(args: seq<string>) {
    var syntax := new B3CliSyntax();
    var cliResult := CLI.Parse(syntax, args);
    if cliResult.Failure? {
      print cliResult.error, "\n";
      return;
    }
    var cli := cliResult.value;
    
    var rawb3;
    match |cli.files| {
      case 0 =>
        print "No files given on command line\n";
        return;
      case 1 =>
        var r := ReadAndParseProgram(cli.files[0]);
        if r.IsFailure() {
          print r.error, "\n";
          return;
        }
        rawb3 := r.value;
      case _ =>
        print "Only 1 filename is supported\n";
        return;
    }

    if "print" in cli.options {
      Printer.Program(rawb3);
    }
    if cli.verb == Parse {
      return;
    }

    var resultResolver := ResolveAndTypeCheck(rawb3, cli);
    if resultResolver.IsFailure() {
      print resultResolver.error, "\n";
      return;
    }
    var b3 := resultResolver.value;
    if cli.verb == Resolve {
      return;
    }

    Verifier.Verify(b3, cli);
  }

  method ReadAndParseProgram(filename: string) returns (r: Result<RawAst.Program, string>) {
    var input :- FileIO.ReadUTF8FromFile(filename);
    var parseResult := SB.Apply(Parser.TopLevel, input);
    var b3 :- match parseResult {
      case ParseSuccess(value, remaining) => Success(value)
      case ParseFailure(_, _) => Failure(SB.FailureToString(input, parseResult))
    };
   return Success(b3);
  }

  method ResolveAndTypeCheck(rawb3: RawAst.Program, cli: CLI.CliResult) returns (r: Result<Ast.Program, string>)
    ensures r.Success? ==> var b3 := r.value;
      b3.WellFormed() && TypeChecker.TypeCorrect(b3) && StaticConsistency.Consistent(b3)
  {
    var b3 :- Resolver.Resolve(rawb3);

    if "rprint" in cli.options {
      ResolvedPrinter.Program(b3);
    }


    var outcome := TypeChecker.TypeCheck(b3);
    if outcome.IsFailure() {
      return Failure(outcome.error);
    }

    outcome := StaticConsistency.CheckConsistent(b3);
    if outcome.IsFailure() {
      return Failure(outcome.error);
    }

    return Success(b3);
  }
}