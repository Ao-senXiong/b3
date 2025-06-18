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
    .I_I(RecMapAExprs("requires"))
    .I_I(RecMapAExprs("ensures"))
    .I_I(RecMapStmt("block").Option())
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

  // ----- Parsing gallery

  datatype RecUnion = UStmt(stmt: Stmt) | UAExprs(aexprs: List<AExpr>) | UExpr(expr: Expr)
  type RecSel = RecMapSel<RecUnion>

  function BMap<T, U>(b: B<T>, f: T -> Option<U>): B<U> {
    B(YMap(b.apply, f))
  }

  opaque function YMap<R, U>(underlying: P.Parser<R>, mappingFunc: R -> Option<U>): P.Parser<U> {
    (input: Input) =>
      var (result, remaining) :- underlying(input);
      match mappingFunc(result)
      case None => P.ParseFailure(FailureLevel.Fatal, P.FailureData("mismatched type of parser production", remaining, None))
      case Some(u) => P.ParseSuccess(u, remaining)
  }

  function parseSelStmt(c: RecSel, productionName: string): B<Stmt> {
    BMap(c(productionName), (ru: RecUnion) => if ru.UStmt? then Some(ru.stmt) else None)
  }

  function parseSelAExprs(c: RecSel, productionName: string): B<List<AExpr>> {
    BMap(c(productionName), (ru: RecUnion) => if ru.UAExprs? then Some(ru.aexprs) else None)
  }

  function parseSelExpr(c: RecSel, productionName: string): B<Expr> {
    BMap(c(productionName), (ru: RecUnion) => if ru.UExpr? then Some(ru.expr) else None)
  }

  const gallery: map<string, RecMapDef<RecUnion>> := map[
      "block" := RecMapDef(0, (c: RecSel) => parseUnlabeledBlockStmt(c).M(s => UStmt(s))),
      "if-tail" := RecMapDef(0, (c: RecSel) => parseIfTail(c).M(s => UStmt(s))),
      "requires" := RecMapDef(0, (c: RecSel) => parseAExprList("requires", c).M(aexprs => UAExprs(aexprs))),
      "ensures" := RecMapDef(0, (c: RecSel) => parseAExprList("ensures", c).M(aexprs => UAExprs(aexprs))),
      "invariant" := RecMapDef(0, (c: RecSel) => parseAExprList("invariant", c).M(aexprs => UAExprs(aexprs)))
    ]

  function RecMapStmt(productionName: string): B<Stmt> {
    BMap(RecMap(gallery, productionName), (ru: RecUnion) => if ru.UStmt? then Some(ru.stmt) else None)
  }

  function RecMapAExprs(productionName: string): B<List<AExpr>> {
    BMap(RecMap(gallery, productionName), (ru: RecUnion) => if ru.UAExprs? then Some(ru.aexprs) else None)
  }

  function RecMapExpr(productionName: string): B<Expr> {
    BMap(RecMap(gallery, productionName), (ru: RecUnion) => if ru.UExpr? then Some(ru.expr) else None)
  }

  // ----- Statements

  function parseUnlabeledBlockStmt(c: RecSel): B<Stmt> {
    T("{").e_I(parseStmt(c).Rep()).I_e(T("}")).M(stmts => Block(AnonymousLabel, stmts))
  }

  function parseStmt(c: RecSel): B<Stmt> {
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
      T("forall").e_I(parseIdType).I_I(parseSelStmt(c, "block")).M3(Unfold3l, (name, typ, body) => AForall(Variable(name, typ, VariableKind.Bound), body)),
      T("if").e_I(parseIfTail(c)),
      T("loop").e_I(parseSelAExprs(c, "invariant")).I_I(parseSelStmt(c, "block")).M2(MId, (invariants, body) => Loop(AnonymousLabel, invariants, body)), // TODO: label
      Nothing.M(_ => Return) // TODO (assign)
    ])
  }

  function parseIfTail(c: RecSel): B<Stmt> {
    Or([
      T("{").e_I(parseCase(c).Rep()).I_e(T("}")).M(cases => IfCase(cases)),
      parseExpr.I_I(parseSelStmt(c, "block")).I_e(T("else")).I_I(Or([
        T("if").e_I(parseSelStmt(c, "if-tail")),
        parseSelStmt(c, "block")
      ]))
      .M3(Unfold3l, (cond, thn, els) => If(cond, thn, els)) // TODO: optional `else`
    ])
  }

  function parseCase(c: RecSel): B<Case> {
    T("case").e_I(parseExpr).I_e(T("=>")).I_I(parseSelStmt(c, "block")).M2(MId, (cond, body) => Case(cond, body))
  }

  // ----- Expressions

  function parseAExprList(keyword: string, c: RecSel): B<List<AExpr>> {
    parseAExpr(keyword, c).Rep().M(aexprs => List.FromSeq(aexprs))
  }

  function parseAExpr(keyword: string, c: RecSel): B<AExpr> {
    T(keyword).e_I(Or([
      parseSelStmt(c, "block").M(stmt => AAssertion(stmt)),
      parseExpr.M(e => AExpr(e))
    ]))
  }

  const parseExpr: B<Expr> :=
    Nat.I_e(W).M(n => Const(n)) // TODO
}