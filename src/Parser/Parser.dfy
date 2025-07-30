module Parser {
  export
    provides TopLevel
    provides StringBuilders, RawAst

  import opened Std.Parsers.StringBuilders
  import opened Std.Wrappers
  import opened Basics
  import opened RawAst
  import Types
  import Std.Collections.Seq

  // Helpful error message about what it would have expected after repeatedly
  // parsing underlying
  function RepTill<T, U>(underlying: B<T>, consumeAfter: B<U>): B<seq<T>> {
    underlying.Rep().I_e(Or([consumeAfter.M(_ => ()), underlying.M(_ => ())]))
  }

  const TopLevel: B<Program> :=
    W.e_I(RepTill(parseTopLevelDecl.I_e(W), EOS)).M(
      decls =>
        var (tt, pp) := SeparateTopLevelDecls(decls);
        Program(tt, pp))

  // ----- Parser helpers

  // Parse `b`. If it succeeds, wrap `Some(_)`, reset the input, and return success.
  // If it fails with a recoverable error, return `None` and reset the input.
  // If it fails fatally, return the failure.
  function Lookahead<R>(b: B<R>): B<Option<R>> {
    B((input: Input) =>
        var p := b.apply(input);
        if p.IsFatalFailure() then
          P.ParseFailure(p.level, p.data)
        else if p.IsFailure() then
          P.ParseSuccess(None, input) // don't consume any input
        else
          P.ParseSuccess(Some(p.result), input) // don't consume any input
    )
  }

  // Parse `b`. If it succeeds, wrap `Some(_)` and return success.
  // If it fails with a recoverable error, return the failure, but reset the input.
  // If it fails fatally, return the failure.
  function Try<R>(b: B<R>): B<Option<R>> {
    B((input: Input) =>
        var p := b.apply(input);
        if p.IsFatalFailure() then
          P.ParseFailure(p.level, p.data)
        else if p.IsFailure() then
          P.ParseSuccess(None, input) // don't consume any input
        else
          P.ParseSuccess(Some(p.result), p.remaining) // consume input
    )
  }

  // Unless there's a fatal error in trying `b`, either perform all of `b` successfully
  // or return its failure without consuming input.
  function Atomic<R>(b: B<R>): B<R> {
    B((input: Input) =>
        var p := b.apply(input);
        if p.IsFailure() && !p.IsFatal() then
          P.ParseFailure(p.level, p.data.(remaining := input)) // reset input
        else
          p
    )
  }

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
  const identifierChar := canStartIdentifierChar + "0123456789_$."

  const parseIdentifierChar: B<char> := CharTest((c: char) => c in identifierChar, "identifier character")
  const parseIdentifierRaw: B<string> := // TODO: this should fail if the identifier is a keyword
    CharTest((c: char) => c in canStartIdentifierChar, "identifier start character").Then(
      (c: char) =>
        parseIdentifierChar.Rep().M((s: string) => [c] + s))
  const parseId: B<string> := parseIdentifierRaw.I_e(W)

  // T = token, that is, the string `s` followed by some non-identifier character (the non-identifier character is not consumed)
  // The characters in `s` are expected to be identifier characters
  function T(s: string): B<string> {
    S(s).I_e(
      Lookahead(parseIdentifierChar).Then(
        (opt: Option<char>) =>
          if opt.Some? then FailWith<()>("keyword followed by identifier character", FailureLevel.Recoverable) else Nothing)
    )
    .I_e(W)
  }

  function Sym(s: string): B<string> {
    S(s).I_e(W)
  }

  function parseParenthesized<X>(parser: B<X>): B<X> {
    S("(").I_e(W).e_I(parser).I_e(S(")")).I_e(W)
  }

  function parseCommaDelimitedSeq<X>(parser: B<X>): B<seq<X>> {
    parser.RepSep(S(",").I_e(W))
  }

  function Unfold3l<X, Y, Z>(r: ((X, Y), Z)): (X, Y, Z) {
    (r.0.0, r.0.1, r.1)
  }

  // ----- Top-level declarations

  datatype TopLevelDecl = TType(typeDecl: Types.TypeName) | TProc(procDecl: Procedure)

  const parseTopLevelDecl: B<TopLevelDecl> :=
    Or([
         parseTypeDecl.M(decl => TType(decl)),
         parseProcDecl.M(decl => TProc(decl))
       ])

  function SeparateTopLevelDecls(decls: seq<TopLevelDecl>): (seq<Types.TypeName>, seq<Procedure>) {
    if decls == [] then ([], []) else
    var (tt, pp) := SeparateTopLevelDecls(decls[1..]);
    match decls[0]
    case TType(typeDecl) => ([typeDecl] + tt, pp)
    case TProc(procDecl) => (tt, [procDecl] + pp)
  }

  const parseTypeDecl: B<Types.TypeName> :=
    T("type").e_I(parseId)

  const parseProcDecl: B<Procedure> :=
    T("procedure")
    .e_I(parseId).Then(
      name =>
        parseParenthesized(
          parseCommaDelimitedSeq(parseFormal)).Then(
          formals =>
            var c := GetRecMapSel(gallery);
            parseAExprSeq("requires", c).Then(
              pre =>
                parseAExprSeq("ensures", c).Then(
                  post =>
                    RecMap(gallery, "block").Option().M(
                      optBody =>
                        Procedure(name, formals, pre, post, optBody)
                    )
                )
            )
        )
    )

  const parseParameterMode: B<ParameterMode> :=
    Or([
         T("inout").M(_ => ParameterMode.InOut),
         T("out").M(_ => ParameterMode.Out),
         Nothing.M(_ => ParameterMode.In)
       ])

  const parseFormal: B<Parameter> :=
    parseParameterMode.Then(
      (mode: ParameterMode) =>
        parseIdType.M2(MId, (name, typ) => Parameter(name, mode, typ))
    )

  const parseIdType: B<(string, string)> :=
    parseId.I_e(Sym(":")).I_I(parseId)

  // ----- Parsing gallery

  type RecSel = RecMapSel<Stmt>

  const gallery: map<string, RecMapDef<Stmt>> :=
    map[
      "block" := RecMapDef(
        0, (c: RecSel) =>
          Sym("{").e_I(RepTill(parseStmt(c), Sym("}"))).M(stmts => Block(stmts))),
      "stmt" := RecMapDef(1, (c: RecSel) => parseStmt(c)),
      "if-cont" := RecMapDef(0, (c: RecSel) => parseIfCont(c)),
      "loop" := RecMapDef(0, (c: RecSel) => parseLoop(c))
    ]

  function GetRecMapSel<R(!new)>(underlying: map<string, RecMapDef<R>>): RecMapSel<R> {
    (fun: string) => RecMap(underlying, fun)
  }

  // ----- Statements

  function parseStmt(c: RecSel): B<Stmt> {
    Or([
         T("var").e_I(parseVariableDeclaration(true, c)),
         T("val").e_I(parseVariableDeclaration(false, c)),
         T("exit").e_I(parseOptionalExitArgument()).M(optionalLabel => Exit(optionalLabel)),
         T("return").M(_ => Return),
         T("check").e_I(parseExpr).M(e => Check(e)),
         T("assume").e_I(parseExpr).M(e => Assume(e)),
         T("assert").e_I(parseExpr).M(e => Assert(e)),
         T("probe").e_I(parseExpr).M(e => Probe(e)),
         T("forall").e_I(parseIdType).I_I(c("block")).M3(Unfold3l, (name, typ, body) => AForall(name, typ, body)),
         c("block"),
         T("if").e_I(parseIfCont(c)),
         c("loop"),
         Atomic(parseId.I_e(Sym(":="))).I_I(parseExpr).M2(MId, (lhs, rhs) => Assign(lhs, rhs)),
         Atomic(parseId.I_e(Sym(":"))).I_I(Or([c("block"), c("loop")])).M2(MId, (lbl, stmt) => LabeledStmt(lbl, stmt)),
         Atomic(parseId.I_e(Sym("("))).I_I(parseCommaDelimitedSeq(parseCallArgument)).I_e(Sym(")")).M2(MId, (name, args) => Call(name, args))
       ])
  }

  function parseVariableDeclaration(isMutable: bool, c: RecSel): B<Stmt> {
    parseIdType.M2(MId, (name: string, typ: string) => Variable(name, isMutable, typ)).
    I_I(Sym(":=").e_I(parseExpr).Option()).
    I_I(c("stmt").Rep()).M3(Unfold3l, (v, init, stmts) =>
                              VarDecl(v, init, Block(stmts)))
  }

  function parseOptionalExitArgument(): B<Option<string>> {
    Lookahead(parseId.I_e(Or([Sym(":="), Sym(":"), Sym("(")]))).Then((maybe: Option<string>) =>
                                                                       if maybe.Some? then Nothing.M(_ => None) else parseId.Option()
    )
  }

  function parseIfCont(c: RecSel): B<Stmt> {
    Or([
         parseCase(c).I_I(parseCase(c).Rep()).M2(MId, (caseHead, caseTail) => IfCase([caseHead] + caseTail)),
         parseExpr.I_I(c("block")).I_I(
           Or([
                T("else").e_I(
                  Or([
                       T("if").e_I(c("if-cont")),
                       c("block")
                     ])),
                Nothing.M(_ => Block([]))
              ])).M3(Unfold3l, (cond, thn, els) => If(cond, thn, els))
       ])
  }

  function parseCase(c: RecSel): B<Case> {
    T("case").e_I(parseExpr).I_I(c("block")).M2(MId, (cond, body) => Case(cond, body))
  }

  function parseLoop(c: RecSel): B<Stmt> {
    T("loop")
    .e_I(parseAExprSeq("invariant", c))
    .I_I(c("block"))
    .M2(MId, (invariants, body) => Loop(invariants, body))
  }

  const parseCallArgument: B<CallArgument> :=
    Or([
         T("out").e_I(parseId).M(name => CallArgument(ParameterMode.Out, IdExpr(name))),
         T("inout").e_I(parseId).M(name => CallArgument(ParameterMode.InOut, IdExpr(name))),
         parseExpr.M(e => CallArgument(ParameterMode.In, e))
       ])

  // ----- Expressions

  function parseAExprSeq(keyword: string, c: RecSel): B<seq<AExpr>> {
    parseAExpr(keyword, c).Rep()
  }

  function parseAExpr(keyword: string, c: RecSel): B<AExpr> {
    T(keyword).e_I(
      Or([
           c("block").M(stmt => AAssertion(stmt)),
           parseExpr.M(e => AExpr(e))
         ]))
  }

  const parseExpr: B<Expr> :=
    Or([
         Nat.I_e(W).M(n => IConst(n)),
         T("false").M(_ => BConst(false)),
         T("true").M(_ => BConst(true)),
         parseId.M(name => IdExpr(name))
       ])
}