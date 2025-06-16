module B3 {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
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
    } else {
      Printer.Program(r.value);
    }
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

  method TestProgram() returns (b3: Program) {
    var types := {};

    var x := Variable("x", Types.IntType, VariableKind.In);
    var y := Variable("y", Types.IntType, VariableKind.InOut);
    var z := Variable("z", Types.IntType, VariableKind.Out);
    var body := Block(AnonymousLabel, [Check(Expr.CreateTrue())]);
    var p := Procedure("Test", [x, y, z], Nil, Nil, Some(body));

    var procedures := {p};
    b3 := Program(types, procedures);
  }
}