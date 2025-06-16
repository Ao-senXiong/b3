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

  const parseIdentifier: B<string> :=
    CharTest((c: char) => c in canStartIdentifierChar, "[" + canStartIdentifierChar + "]").Then((c: char) =>
      CharTest((c: char) => c in canStartIdentifierChar || c in "_?$", "Identifier character").Rep().M((s: string) => [c] + s))

  // T = token, that is, the string `s` followed by some non-identifier character
  function T(s: string): B<string> {
    S(s).I_e(W.If(Except(canStartIdentifierChar)))
  }

  function parseParentheses<X>(parser: B<X>): B<X> {
    S("(").I_e(W).e_I(parser).I_e(S(")")).I_e(W)
  }

  function parseCommaDelimitedList<X>(parser: B<X>): B<seq<X>> {
    parser.RepSep(S(",").I_e(W))
//    parser.I_I(S(",").I_e(W).e_I(parser).Rep()).M2(MId, (head, tail) => [head] + tail)
  }

  // ----- Top-level declarations

  const parseProcDecl: B<Procedure> :=
    T("procedure")
    .e_I(parseIdentifier).I_e(W)
    .I_I( parseParentheses( parseCommaDelimitedList(parseFormal ) ))
    .M2(MId, (name, formals) => Procedure(name, formals, Nil, Nil, None))
  
  const parseFormal: B<Variable> := parseIdentifier.I_e(W).M(s => Variable(s, Types.IntType, VariableKind.In))
}