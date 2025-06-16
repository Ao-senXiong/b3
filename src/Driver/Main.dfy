module B3 {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import Types
  import Printer

  method Main() {
    var b3 := TestProgram();
    Printer.Program(b3);
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