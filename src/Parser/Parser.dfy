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

  const TopLevel: B<Program> :=
    W.e_I(parseTopLevelDecl.I_e(W).Rep()).End().M(decls =>
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
  const parseIdentifierRaw: B<string> :=
    CharTest((c: char) => c in canStartIdentifierChar, "identifier start character").Then((c: char) =>
      parseIdentifierChar.Rep().M((s: string) => [c] + s))
  const parseId: B<string> := parseIdentifierRaw.I_e(W)

  // T = token, that is, the string `s` followed by some non-identifier character (the non-identifier character is not consumed)
  // The characters in `s` are expected to be identifier characters
  function T(s: string): B<string> {
    S(s).I_e(
      Lookahead(parseIdentifierChar).Then((opt: Option<char>) =>
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
    .e_I(parseId).Then(name =>
      parseParenthesized(parseCommaDelimitedSeq(parseFormal)).Then(formals =>
        ParseWithContext(gallery, (c: RecSel) => parseAExprSeq("requires", c)).Then(pre =>
          ParseWithContext(gallery, (c: RecSel) => parseAExprSeq("ensures", c)).Then(post =>
            RecMap(gallery, "block").Option().M(optBody =>
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
    parseParameterMode.Then((mode: ParameterMode) =>
      parseIdType.M2(MId, (name, typ) =>
        Parameter(mode, Variable(name, typ, mode.IsOutgoing()))
      )
    )

  const parseIdType: B<(string, string)> :=
    parseId.I_e(Sym(":")).I_I(parseId)

  // ----- Parsing gallery

  type RecSel = RecMapSel<Stmt>

  const gallery: map<string, RecMapDef<Stmt>> := map[
      "block" := RecMapDef(0, (c: RecSel) => parseUnlabeledBlockStmt(c).M(s => s)),
      "stmt" := RecMapDef(0, (c: RecSel) => parseStmt(c).M(s => s)),
      "if-cont" := RecMapDef(0, (c: RecSel) => parseIfCont(c).M(s => s))
    ]

  function ParseWithContext<G(!new), R>(underlyingGallery: map<string, RecMapDef<G>>, parser: RecMapSel<G> -> B<R>): B<R> {
    var b := MyRecMapSpecialized(underlyingGallery, parser);
    B((input: Input) =>
      var (result, remaining) :- b.apply(input);
      P.ParseSuccess(result, remaining))
  }

  function MyRecMapSpecialized<G(!new), R>(underlyingGallery: map<string, RecMapDef<G>>, parser: RecMapSel<G> -> B<R>): B<R> {
    B((input: Input) =>
      var callback: P.ParserSelector<G> := Callback(UnderlyingP(underlyingGallery), "<context>", 0, P.A.Length(input));
      var c: RecMapSel<G> := (name: string) => B(callback(name));
      parser(c).apply(input)
    )
  }

  function UnderlyingP<R>(underlying: map<string, RecMapDef<R>>): map<string, P.RecursiveDef<R>> {
    map k <- underlying ::
      P.RecursiveDef(
        underlying[k].order,
        (selector: P.ParserSelector<R>) =>
          underlying[k].definition(
            (name: string) => B(selector(name))                  
          ).apply)
  }

  function Callback<R(!new)>(underlying: map<string, P.RecursiveDef<R>>, fun: string, orderFun: nat, initialInputLength: nat): P.ParserSelector<R> {
    (fun': string) =>
      if fun' !in underlying.Keys then
        P.FailWith(fun' + " not defined", P.Fatal)
      else
        var orderFun', definitionFun' := underlying[fun'].order, underlying[fun'].definition;
        (remaining: Input) =>
          if P.A.Length(remaining) < initialInputLength || (P.A.Length(remaining) == initialInputLength && orderFun' < orderFun) then
            P.RecursiveMap_(underlying, fun', remaining)
          else if P.A.Length(remaining) == initialInputLength then
            P.ParseFailure(P.Recoverable,
              P.FailureData(
                "non-progressing recursive call requires that order of '" + fun' + "' (" + P.Strings.OfInt(orderFun') + ") " +
                "is lower than the order of '" + fun + "' (" + P.Strings.OfInt(orderFun) + ")",
              remaining, Option.None))
          else
            P.ParseFailure(P.Fatal, P.FailureData("parser did not return a suffix of the input", remaining, Option.None))
  }

  // ----- Statements

  function parseUnlabeledBlockStmt(c: RecSel): B<Stmt> {
    Sym("{").e_I(parseStmt(c).Rep()).I_e(Sym("}")).M(stmts => Block(AnonymousLabel, stmts))
  }

  function parseStmt(c: RecSel): B<Stmt> {
    Or([
      T("var").e_I(parseIdType).M2(MId, (name, typ) => VarDecl(Variable(name, typ, true))),
      T("val").e_I(parseIdType).I_e(Sym(":=")).I_I(parseExpr).M3(Unfold3l, (name, typ, rhs) => ValDecl(Variable(name, typ, false), rhs)),
      T("exit").e_I(parseId).M(name => Exit(NamedLabel(name))),
      T("return").M(_ => Return),
      T("check").e_I(parseExpr).M(e => Check(e)),
      T("assume").e_I(parseExpr).M(e => Assume(e)),
      T("assert").e_I(parseExpr).M(e => Assert(e)),
      T("probe").e_I(parseExpr).M(e => Probe(e)),
      T("forall").e_I(parseIdType).I_I(c("block")).M3(Unfold3l, (name, typ, body) => AForall(Variable(name, typ, false), body)),
      T("if").e_I(parseIfCont(c)),
      parseOptionalLabel(Sym("{")).Then((optLbl: Option<string>) =>
        c("block").M((s: Stmt) =>
          if optLbl.Some? && s.Block? then
            Block(NamedLabel(optLbl.value), s.stmts)
          else
            s
        )
      ),
      parseOptionalLabel(T("loop")).Then((optLbl: Option<string>) =>
        T("loop").e_I(parseAExprSeq("invariant", c)).I_I(c("block"))
        .M2(MId, (invariants, body) => Loop(match optLbl case Some(name) => NamedLabel(name) case _ => AnonymousLabel, invariants, body))
      ),
      Atomic(parseId.I_e(Sym(":="))).I_I(parseExpr).M2(MId, (lhs, rhs) => Assign(lhs, rhs)),
      Atomic(parseId.I_e(Sym("("))).I_I(parseCommaDelimitedSeq(parseCallArgument)).I_e(Sym(")")).M2(MId, (name, args) => Call(name, args))
    ])
  }

  function parseOptionalLabel<R>(next: B<R>): B<Option<string>> {
    B((input: Input) =>
      var p := Try(parseId.I_e(Sym(":"))).apply(input);
      if p.IsFailure() || p.result == None then
        p
      else
        // look ahead to parse `next`
        var q := next.apply(p.remaining);
        if q.IsFatalFailure() then
          P.ParseFailure(q.level, q.data)
        else if q.IsFailure() then
          P.ParseSuccess(None, input)
        else
          p // return the state after parsing `id :`
    )
  }

  function parseIfCont(c: RecSel): B<Stmt> {
    Or([
      Sym("{").e_I(parseCase(c).Rep()).I_e(Sym("}")).M(cases => IfCase(cases)),
      parseExpr.I_I(c("block")).I_I(Or([
        T("else").e_I(Or([
          T("if").e_I(c("if-cont")),
          c("block")
        ])),
        Nothing.M(_ => Block(AnonymousLabel, []))
      ])).M3(Unfold3l, (cond, thn, els) => If(cond, thn, els))
    ])
  }

  function parseCase(c: RecSel): B<Case> {
    T("case").e_I(parseExpr).I_e(Sym("=>")).I_I(
      c("stmt").Rep().M(stmts => Block(AnonymousLabel, stmts))
    ).M2(MId, (cond, body) => Case(cond, body))
  }

  const parseCallArgument: B<CallArgument> :=
    Or([
      T("out").e_I(parseId).M(name => ArgLValue(ParameterMode.Out, name)),
      T("inout").e_I(parseId).M(name => ArgLValue(ParameterMode.InOut, name)),
      parseExpr.M(e => ArgExpr(e))
    ])

  // ----- Expressions

  function parseAExprSeq(keyword: string, c: RecSel): B<seq<AExpr>> {
    parseAExpr(keyword, c).Rep()
  }

  function parseAExpr(keyword: string, c: RecSel): B<AExpr> {
    T(keyword).e_I(Or([
      c("block").M(stmt => AAssertion(stmt)),
      parseExpr.M(e => AExpr(e))
    ]))
  }

  const parseExpr: B<Expr> :=
    Or([
      Nat.I_e(W).M(n => Const(n)),
      parseId.M(name => IdExpr(name))
    ])
}