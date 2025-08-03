module B3 {
  import opened Std.Wrappers
  import opened Basics
  import RawAst
  import Types
  import Printer
  import Std.FileIO
  import SB = Std.Parsers.StringBuilders
  import Parser
  import Resolver
  import Ast
  import TypeChecker
  import Verifier
  import StaticConsistency

  method Main(args: seq<string>) {
    if |args| != 2 {
      PrintUsage();
      return;
    }

    var r := ReadAndParseProgram(args[1]);
    if r.IsFailure() {
      print r.error, "\n";
      return;
    }
    var rawb3 := r.value;

    Printer.Program(rawb3);

    print "The program ", if rawb3.WellFormed() then "IS" else "is NOT", " well-formed\n";
    var resultResolver := ResolveAndTypeCheck(rawb3);
    if resultResolver.IsFailure() {
      print resultResolver.error, "\n";
      return;
    }
    var b3 := resultResolver.value;

    Verifier.Verify(b3);
  }

  method PrintUsage() {
    print "Usage: b3 <filename.b3>\n";
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

  method ResolveAndTypeCheck(rawb3: RawAst.Program) returns (r: Result<Ast.Program, string>) {
    var b3 :- Resolver.Resolve(rawb3);

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