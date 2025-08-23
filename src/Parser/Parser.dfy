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
    parser.RepSep(Sym(","))
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
            var c := GetRecMapSel(stmtGallery);
            parseAExprSeq("requires", c).Then(
              pre =>
                parseAExprSeq("ensures", c).Then(
                  post =>
                    RecMap(stmtGallery, "block").Option().M(
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

  type StmtRecSel = RecMapSel<Stmt>
  type ExprRecSel = RecMapSel<Expr>

  const stmtGallery: map<string, RecMapDef<Stmt>> :=
    map[
      "block" := RecMapDef(
        0, (c: StmtRecSel) =>
          Sym("{").e_I(RepTill(parseStmt(c), Sym("}"))).M(stmts => Block(stmts))),
      "stmt" := RecMapDef(1, (c: StmtRecSel) => parseStmt(c)),
      "if-cont" := RecMapDef(0, (c: StmtRecSel) => parseIfCont(c)),
      "loop" := RecMapDef(0, (c: StmtRecSel) => parseLoop(c))
    ]

  const exprGallery: map<string, RecMapDef<Expr>> :=
    map[
      "expr" := RecMapDef(1, (c: ExprRecSel) => parseEquivExpr(c))
    ]

  function GetRecMapSel<R(!new)>(underlying: map<string, RecMapDef<R>>): RecMapSel<R> {
    (fun: string) => RecMap(underlying, fun)
  }

  // ----- Statements

  function parseStmt(c: StmtRecSel): B<Stmt> {
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

  function parseVariableDeclaration(isMutable: bool, c: StmtRecSel): B<Stmt> {
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

  function parseIfCont(c: StmtRecSel): B<Stmt> {
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

  function parseCase(c: StmtRecSel): B<Case> {
    T("case").e_I(parseExpr).I_I(c("block")).M2(MId, (cond, body) => Case(cond, body))
  }

  function parseLoop(c: StmtRecSel): B<Stmt> {
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

  function parseAExprSeq(keyword: string, c: StmtRecSel): B<seq<AExpr>> {
    parseAExpr(keyword, c).Rep()
  }

  function parseAExpr(keyword: string, c: StmtRecSel): B<AExpr> {
    T(keyword).e_I(
      Or([
           c("block").M(stmt => AAssertion(stmt)),
           parseExpr.M(e => AExpr(e))
         ]))
  }

  /* Here is the expression grammar (but not formulated as an LL(1) grammar).
   *
   * Expr ::= ( ImpExpExpr "<==>" )* ImpExpExpr                    // associates to the left
   * ImpExpExpr ::= ImpliesExpr | ExpliesExpr                      // needs disambiguation after parsing one LogicalExpr
   * ImpliesExpr ::= LogicalExpr "==>" ImpliesExpr                 // associates to the right
   * ExpliesExpr ::= ( LogicalExpr "<==" )* LogicalExpr            // associates to the left
   * LogicalExpr ::= AndExpr | OrExpr                              // needs disambiguation after parsing one JunctExpr
   * AndExpr ::= ( JuctExpr "&&" )* JuctExpr                       // associates to the left
   * OrExpr ::= ( JuctExpr "||" )* JuctExpr                        // associates to the left
   * JuctExpr ::= TermExpr [ ( "==" | "!=" | "<" | "<=" | ">=" | ">" ) TermExpr ]
   * TermExpr ::= ( FactorExpr ( "+" | "-" ))* FactorExpr          // associates to the left
   * FactorExpr ::= ( UnaryExpr ( "*" | "/" | "%" ))* UnaryExpr    // associates to the left
   * UnaryExpr ::= ( "!" | "-" )* PrimaryExpr
   * PrimaryExpr ::= EndlessExpr
   *               | AtomicExpr
   * EndlessExpr ::= "if" Expr "then" Expr "else" Expr
   *               | "var" Id ":" Type ":=" Expr ";" Expr
   *               | ( "forall" | "exists" ) Id ":" Type ( "trigger" Expr*, )* "::" Expr
   *               | Id ":" Expr
   * AtomicExpr ::= "false" | "true"
   *              | nat
   *              | "[" literalString ":" Type "]"          // uninterpreted literals
   *              | Id
   *              | Id "(" Expr*, ")"
   *              | "(" Expr ")"
  */

  const parseExpr: B<Expr> := RecMap(exprGallery, "expr")

  function parseEquivExpr(c: ExprRecSel): B<Expr> {
    parseImpExpExpr(c).Then(e0 =>
      Sym("<==>").e_I(parseImpExpExpr(c)).Rep().M(exprs =>
        FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.Equiv, [a, b]))
      )
    )
  }

  function parseImpExpExpr(c: ExprRecSel): B<Expr> {
    parseLogicalExpr(c).Then(e0 =>
      Or([
        Sym("==>").e_I(parseLogicalExpr(c).RepSep(Sym("==>")))
          .M(exprs => FoldRight(exprs, e0, (a, b) => OperatorExpr(Operator.LogicalImp, [a, b]))),
        Sym("<==").e_I(parseLogicalExpr(c).RepSep(Sym("<==")))
          .M(exprs => FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.LogicalImp, [b, a]))),
        Nothing.M(_ => e0)
      ])
    )
  }

  function parseLogicalExpr(c: ExprRecSel): B<Expr> {
    parseJuctExpr(c).Then(e0 =>
      Or([
        Sym("&&").e_I(parseJuctExpr(c).RepSep(Sym("&&")))
          .M(exprs => FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.LogicalAnd, [a, b]))),
        Sym("||").e_I(parseJuctExpr(c).RepSep(Sym("||")))
          .M(exprs => FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.LogicalOr, [a, b]))),
        Nothing.M(_ => e0)
      ])
    )
  }

  function parseJuctExpr(c: ExprRecSel): B<Expr> {
    parseTermExpr(c).Then(e0 =>
      parseComparisonOperator.I_I(parseTermExpr(c)).Option().M((opt: Option<((Operator, bool), Expr)>) =>
        match opt
        case None => e0
        case Some(((op, false), e1)) => OperatorExpr(op, [e0, e1])
        case Some(((op, true), e1)) => OperatorExpr(op, [e1, e0])
    ))
  }
  const parseComparisonOperator: B<(Operator, bool)> :=
    Or([
      Sym("==").M(_ => (Operator.Eq, false)),
      Sym("!=").M(_ => (Operator.Neq, false)),
      Sym("<").M(_ => (Operator.Less, false)),
      Sym("<=").M(_ => (Operator.AtMost, false)),
      Sym(">=").M(_ => (Operator.AtMost, true)),
      Sym(">").M(_ => (Operator.Less, true))
    ])

  function parseTermExpr(c: ExprRecSel): B<Expr> {
    parseFactorExpr(c).Then(e0 =>
      Or([
        Sym("+").M(_ => Operator.Plus),
        Sym("-").M(_ => Operator.Minus)
      ]).I_I(parseFactorExpr(c)).Rep()
      .M(opExprs => FoldLeft(e0, opExprs, (a, b: (Operator, Expr)) => OperatorExpr(b.0, [a, b.1])))
    )
  }

  function parseFactorExpr(c: ExprRecSel): B<Expr> {
    parseUnaryExpr(c).Then(e0 =>
      Or([
        Sym("*").M(_ => Operator.Times),
        Sym("/").M(_ => Operator.Div),
        Sym("%").M(_ => Operator.Mod)
      ]).I_I(parseUnaryExpr(c)).Rep()
      .M(opExprs => FoldLeft(e0, opExprs, (a, b: (Operator, Expr)) => OperatorExpr(b.0, [a, b.1])))
    )
  }

  function parseUnaryExpr(c: ExprRecSel): B<Expr> {
    Or([
      Sym("!").M(_ => Operator.LogicalNot),
      Sym("-").M(_ => Operator.UnaryMinus)
    ]).Rep().I_I(parsePrimaryExpr(c)).M2(MId, (unaryOperators, expr) =>
      FoldRight(unaryOperators, expr, (op, e) => OperatorExpr(op, [e]))
    )
  }

  function parsePrimaryExpr(c: ExprRecSel): B<Expr> {
    Or([
      T("if").e_I(c("expr")).Then(guard =>
        c("expr").I_I(T("else").e_I(c("expr"))).M2(MId, (thn, els) => OperatorExpr(IfThenElse, [guard, thn, els]))
      ),
      T("val").e_I(parseIdType.Then(p => var (name: string, typ: string) := p;
        Sym(":=").e_I(c("expr")).I_I(c("expr")).M2(MId, (rhs, body) => LetExpr(name, typ, rhs, body)))
      ),
      Or([T("forall").M(_ => true), T("exists").M(_ => false)]).Then(universal =>
        parseIdType.Then(p => var (name: string, typ: string) := p;
          parseTrigger(c).Rep().Then(triggers =>
            Sym("::").e_I(c("expr")).M(body => QuantifierExpr(universal, name, typ, triggers, body))
          )
        )
      ),
      parseAtomicExpr(c)
    ])
  }

  function parseTrigger(c: ExprRecSel): B<Trigger> {
    T("trigger").e_I(parseCommaDelimitedSeq(c("expr"))).M(exprs => Trigger(exprs))
  }

  function parseAtomicExpr(c: ExprRecSel): B<Expr> {
    Or([
      T("false").M(_ => BConst(false)),
      T("true").M(_ => BConst(true)),
      Nat.I_e(W).M(n => IConst(n)),
      // TODO:  "[" literalString ":" Type "]"          // uninterpreted literals
      parseId.Then(name =>
        Or([
          Sym("(").e_I(parseCommaDelimitedSeq(c("expr"))).I_e(Sym(")"))
            .M(args => FunctionCallExpr(name, args)),
          Sym(":").e_I(c("expr")).M(e => LabeledExpr(name, e)),
          Nothing.M(_ => IdExpr(name))
        ])),
      Sym("(").e_I(c("expr")).I_e(Sym(")"))
    ])
  }
}