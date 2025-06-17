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

  function Unfold3l<X, Y, Z>(r: ((X, Y), Z)): (X, Y, Z) {
    (r.0.0, r.0.1, r.1)
  }

  function Unfold3r<X, Y, Z>(r: (X, (Y, Z))): (X, Y, Z) {
    (r.0, r.1.0, r.1.1)
  }

  function Unfold5l<A, B, C, D, E>(r: ((((A, B), C), D), E)): (A, B, C, D, E) {
    (r.0.0.0.0, r.0.0.0.1, r.0.0.1, r.0.1, r.1)
  }

  // ----- Top-level declarations

  const parseProcDecl: B<Procedure> :=
    T("procedure")
    .e_I(parseId)
    .I_I(parseParenthesized(parseCommaDelimitedList(parseFormal)))
    .I_I(parseAExprList("requires"))
    .I_I(parseAExprList("ensures"))
    .I_I(parseUnlabeledBlockStmt.Option())
    .M(r =>
      var (name, formals, pre, post, optBody) := Unfold5l(r);
      Procedure(name, formals, pre, post, optBody)
    )
  
  const parseFormal: B<Variable> :=
    Or([
      T("inout").M(_ => VariableKind.InOut),
      T("out").M(_ => VariableKind.Out),
      Nothing.M(_ => VariableKind.In)
    ])
    .I_I(parseIdType)
    .M3(Unfold3r, (kind, name, typ) => Variable(name, typ, kind))

  const parseIdType: B<(string, string)> :=
    parseId.I_e(T(":")).I_I(parseId)

  // ----- Statements

  const parseUnlabeledBlockStmt: B<Stmt> :=
    T("{").e_I(parseStmt.Rep()).I_e(T("}")).M(stmts => Block(AnonymousLabel, stmts))

  const parseStmt: B<Stmt> :=
    Or([
      T("var").e_I(parseIdType).M2(MId, (name, typ) => VarDecl(Variable(name, typ, VariableKind.Local))),
      T("val").e_I(parseIdType).I_e(T(":=")).I_I(parseExpr).M3(Unfold3l, (name, typ, rhs) => ValDecl(Variable(name, typ, VariableKind.Let), rhs)),
      T("exit").e_I(parseId).M(name => Exit(NamedLabel(name))),
      T("return").M(_ => Return),
      T("{").M(_ => Return), // TODO (also remember to consider label)
      T("call").M(_ => Return), // TODO
      T("check").e_I(parseExpr).M(e => Check(e)),
      T("assume").e_I(parseExpr).M(e => Assume(e)),
      T("assert").e_I(parseExpr).M(e => Assert(e)),
      T("probe").e_I(parseExpr).M(e => Probe(e)),
//Rec:      T("forall").e_I(parseIdType).I_I(parseUnlabeledBlockStmt).M3(Unfold3l, (name, typ, body) => AForall(Variable(name, typ, VariableKind.Bound), body)),
//Rec:      T("if").e_I(parseIfContinuation),
//Rec:      T("loop").e_I(parseAExprList("invariant")).I_I(parseUnlabeledBlockStmt).M2(MId, (invariants, body) => Loop(AnonymousLabel, invariants, body)), // TODO: label
      Nothing.M(_ => Return) // TODO (assign)
    ])
  
  const parseIfContinuation: B<Stmt> :=
    Or([
      parseCase.Rep().If(T("case")).M(cases => IfCase(cases)),
      parseExpr.I_I(parseUnlabeledBlockStmt).I_e(T("else")).I_I(Or([
//Rec:        T("if").e_I(parseIfContinuation),
        parseUnlabeledBlockStmt
      ]))
      .M3(Unfold3l, (cond, thn, els) => If(cond, thn, els)) // TODO: variations of `else`
    ])

  const parseCase: B<Case> :=
    T("case").e_I(parseExpr).I_e(T("=>")).I_I(parseUnlabeledBlockStmt).M2(MId, (cond, body) => Case(cond, body))

  // ----- Expressions

  function parseAExprList(keyword: string): B<List<AExpr>> {
    parseAExpr(keyword).Rep().M(aexprs => List.FromSeq(aexprs))
  }

  function parseAExpr(keyword: string): B<AExpr> {
    T(keyword).e_I(Or([
//Rec:      parseUnlabeledBlockStmt.M(stmt => AAssertion(stmt)),
      parseExpr.M(e => AExpr(e))
    ]))
  }

  const parseExpr: B<Expr> :=
    Nat.I_e(W).M(n => Const(n)) // TODO
}