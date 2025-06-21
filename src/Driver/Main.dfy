module B3 {
  import opened Std.Wrappers
  import opened Basics
  import opened RawAst
  import Types
  import Printer
  import Std.FileIO
  import SB = Std.Parsers.StringBuilders
  import Parser

  method Main(args: seq<string>) {
    if |args| != 2 {
      PrintUsage();
      return;
    }

    var r := ReadAndParseProgram(args[1]);
    if r.IsFailure() {
      print r.error;
      return;
    }
    var b3 := r.value;

    Printer.Program(b3);
   }

  method PrintUsage() {
    print "Usage: b3 <filename.b3>\n";
  }

  method ReadAndParseProgram(filename: string) returns (r: Result<Program, string>) {
    var input :- FileIO.ReadUTF8FromFile(filename);
    var parseResult := SB.Apply(Parser.TopLevel, input);
    var b3 :- match parseResult {
      case ParseSuccess(value, remaining) => Success(value)
      case ParseFailure(_, _) => Failure(SB.FailureToString(input, parseResult))
    };
   return Success(b3);
  }
}