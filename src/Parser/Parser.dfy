module Parser {
  export
    provides TopLevel
    provides StringBuilders, Ast

  import opened Std.Parsers.StringBuilders
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import Std.Collections.Seq

  const TopLevel: B<Program> :=
    W.e_I(parseProcDecl.I_e(W).Rep()).End().M(procedures => Program({}, set proc <- procedures))

  // ----- Whitespace

  const notNewline :=
    CharTest((c: char) => c !in "\n", "anything except newline")

  function StringConcat(s: string, t: string): string { s + t }
  
  // W = whitespace or comment
  const W: B<string> :=
    WS.I_I(
      S("//").I_I(notNewline.Rep()).M2(MId, StringConcat)
      .I_I(O([S("\n"), EOS.M(x => "")])).M2(MId, StringConcat)
      .I_I(WS).M2(MId, StringConcat).Rep()
    ).M((wsMore: (string, seq<string>)) => wsMore.0 + Seq.Join(Seq.Map(MId, wsMore.1), ""))

  const canStartIdentifierChar := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

  const parseIdentifierRaw: B<string> :=
    CharTest((c: char) => c in canStartIdentifierChar, "[" + canStartIdentifierChar + "]").Then((c: char) =>
      CharTest((c: char) => c in canStartIdentifierChar || c in "_?$", "Identifier character").Rep().M((s: string) => [c] + s))
  const parseId: B<string> := parseIdentifierRaw.I_e(W)

  // T = token, that is, the string `s` followed by some non-identifier character
  function T(s: string): B<string> {
    S(s).I_e(W.If(Except(canStartIdentifierChar)))
  }

  function parseParenthesized<X>(parser: B<X>): B<X> {
    S("(").I_e(W).e_I(parser).I_e(S(")")).I_e(W)
  }

  function parseCommaDelimitedList<X>(parser: B<X>): B<seq<X>> {
    parser.RepSep(S(",").I_e(W))
  }

  function Unfold3<X, Y, Z>(r: ((X, Y), Z)): (X, Y, Z) {
    (r.0.0, r.0.1, r.1)
  }

  // ----- Top-level declarations

  const parseProcDecl: B<Procedure> :=
    T("procedure")
    .e_I(parseId)
    .I_I(parseParenthesized(parseCommaDelimitedList(parseFormal)))
    .M2(MId, (name, formals) => Procedure(name, formals, Nil, Nil, None))
  
  const parseFormal: B<Variable> :=
    Or([
      T("inout").M(_ => VariableKind.InOut),
      T("out").M(_ => VariableKind.Out)
    ]).Option().M(opt => if opt == None then VariableKind.In else opt.value)
    .I_I(parseId)
    .I_e(T(":")).I_I(parseId)
    .M3(Unfold3, (kind, name, typ) => Variable(name, typ, kind))

  // ----- Statements

//  const parseStmt: B

}