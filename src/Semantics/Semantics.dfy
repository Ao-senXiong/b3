// TODO: enclosing procedures, auto-invariants

module Semantics {
/*****
  import opened Basics
  import opened RawAst
  import opened Values
  import WF = WellFormednessConsequences

  // Big-step semantics

  // The big-step semantics is defined as a relation on State, relating an initial valuation contained where the initial state is a
  // valuation contained in the State(_) variant and the final state is such a valuation, possibly augmented with a target label,
  // or an error.
  //
  // TODO: This first version of a formal semantics is defined on raw programs. This should change to instead be defined on a resolved program.
  datatype State =
    | State(m: Valuation, shadowedVariables: Valuation)
    | AbruptExit(lbl: Label, m: Valuation, shadowedVariables: Valuation)
    | Error
  {
    function ClearShadows(): State
      requires State?
    {
      this.(shadowedVariables := map[])
    }
    function SaveAsShadow(name: string): State
      requires State?
    {
      if name in m then State(m, shadowedVariables[name := m[name]]) else this
    }
    function Update(name: string, val: Value): State
      requires State?
    {
      State(m[name := val], shadowedVariables)
    }
    function Raise(lbl: Label): State
      requires State?
    {
      AbruptExit(lbl, m, shadowedVariables)
    }
    function Lower(lbl: Label): State {
      if AbruptExit? && lbl == this.lbl then State(m, shadowedVariables) else this
    }
    function RestoreScope(orig: State): State
      requires orig.State?
    {
      match this
      case State(m, shadowedVariables) =>
        this.(m := RestoreValuationByScope(m, orig.m.Keys, shadowedVariables), shadowedVariables := orig.shadowedVariables)
      case AbruptExit(_, m, shadowedVariables) =>
        this.(m := RestoreValuationByScope(m, orig.m.Keys, shadowedVariables), shadowedVariables := orig.shadowedVariables)
      case Error =>
        Error
    }
    static function RestoreValuationByScope(m: Valuation, desiredKeys: set<string>, shadowedMap: Valuation): Valuation {
      map x | x in m && x in desiredKeys :: if x in shadowedMap then shadowedMap[x] else m[x]
    }
  }

  // In a program `b3`, the judgment `BigStep(stmt, b3, st, st')` says that it's
  // possible to start `stmt` is state `st` and either not terminate at all or terminate
  // in state `st'`.
  greatest predicate BigStep(stmt: Stmt, b3: Program, st: State, st': State)
    requires WF.Stmt(stmt, b3)
    requires st.State?
  {
    match stmt
    case VarDecl(v) =>
      exists val :: HasType(val, v.typ) && st' == st.SaveAsShadow(v.name).Update(v.name, val)
    case ValDecl(v, rhs) =>
      st' == st.SaveAsShadow(v.name).Update(v.name, rhs.Eval(st.m))
    case Assign(lhs, rhs) =>
      st' == st.Update(lhs, rhs.Eval(st.m))
    case Block(lbl, stmts) =>
      WF.AboutBlock(stmt, b3);
      exists mid :: BigStepSeq(stmts, b3, st.ClearShadows(), mid) && st' == mid.Lower(lbl).RestoreScope(st)
    case Call(name, args) =>
      BigStepCall(stmt, b3, st, st')
    case Check(cond) =>
      if cond.Eval(st.m) == True then st' == st else st' == Error
    case Assume(cond) =>
      cond.Eval(st.m) == True && st' == st
    case Assert(cond) =>
      if cond.Eval(st.m) == True then st' == st else st' == Error
    case AForall(v, body) =>
      FollowsFromWellFormedness(ValidAssertionStatement(stmt)) &&
      var assertions := SeparateAssertion(stmt, AContextEmpty);
      WF.StmtSeq(assertions, b3) && // TODO: follows from SeparateAssertion
      BigStepSeq(assertions, b3, st, st')
    case If(cond, thn, els) =>
      WF.AboutIf(stmt, b3);
      BigStep(if cond.Eval(st.m) == True then thn else els, b3, st, st')
    case IfCase(cases) =>
      WF.AboutIfCase(stmt, b3);
      exists cs <- cases :: cs.cond.Eval(st.m) == True && BigStep(cs.body, b3, st, st')
    case Loop(lbl, invariants, body) =>
      WF.AboutLoop(stmt, b3);
      exists st0 ::
        var checks := SeqMap(invariants, (ae: AExpr) => ae.ToCheckStmt());
        WF.StmtSeq(checks, b3) && // TODO: follows from ToCheckStmt()
        BigStepSeq(checks, b3, st, st0) &&
        if !st0.State? then
          st' == st0
        else
          exists st1 ::
            BigStep(body, b3, st0, st1) &&
            if !st1.State? then
              st' == st1.Lower(lbl)
            else
              BigStep(stmt, b3, st1, st')
    case Exit(lbl) =>
      st' == st.Raise(lbl)
    case Return =>
      st' == st.Raise(ReturnLabel)
    case Probe(e) =>
      st' == st
  }

  greatest predicate BigStepCall(stmt: Stmt, b3: Program, st: State, st': State)
    requires WF.Stmt(stmt, b3)
    requires stmt.Call? && st.State?
  {
    var Call(name, args) := stmt;
    var sh := st.shadowedVariables;
    exists proc <- b3.procedures | proc.name == name ::
      FollowsFromWellFormedness(Stmt.MatchingParameters(proc.parameters, args) && Parameter.UniqueNames(proc.parameters)) &&
      exists entry | ProcEntryParameters(st.m, entry, proc.parameters, args) ::
        var checks := SeqMap(proc.pre, (ae: AExpr) => ae.ToCheckStmt());
        WF.StmtSeq(checks, b3) && // TODO: follows from ToCheckStmt()
        exists st0 | BigStepSeq(checks, b3, State(entry, sh), st0) ::
          || (!st0.State? && st' == st0)
          || (st0.State? &&
              exists exit | ProcExitParameters(entry, exit, proc.parameters, args) ::
                var toAssumeStmt := (ae: AExpr) requires ae.Valid() => ae.ToAssumeStmt();
                FollowsFromWellFormedness(forall ae <- proc.post :: ae.Valid()) &&
                var assumes := SeqMap(proc.post, toAssumeStmt);
                WF.StmtSeq(assumes, b3) && // TODO: follows from ToAssumeStmt()
                exists st1 | BigStepSeq(assumes, b3, State(exit, sh), st1) ::
                  st1.State? && st1 == State(exit, sh) && // this line follows from the definitions of BigStepSeq and ToAssumeStmt
                  WriteBackOutgoingParameters(st.m, sh, exit, st', proc.parameters, args))
  }

  ghost predicate ProcEntryParameters(callState: Valuation, entry: Valuation, parameters: seq<Parameter>, args: seq<CallArgument>)
    requires Stmt.MatchingParameters(parameters, args) && Parameter.UniqueNames(parameters)
  {
    FollowsFromWellFormedness(forall arg <- args :: arg.ArgLValue? ==> arg.name in callState) &&
    entry == map i | 0 <= i < |args| && parameters[i].mode.IsIncoming() :: parameters[i].v.name := args[i].Eval(callState)
  }

  ghost predicate ProcExitParameters(entry: Valuation, exit: Valuation, parameters: seq<Parameter>, args: seq<CallArgument>)
    requires Stmt.MatchingParameters(parameters, args) && Parameter.UniqueNames(parameters)
    ensures ProcExitParameters(entry, exit, parameters, args) ==>
      forall formal <- parameters | formal.mode.IsOutgoing() :: formal.v.name in exit
  {
    var inOuts := set formal <- parameters | formal.mode == InOut :: formal;
    var outgoing := set formal <- parameters | formal.mode.IsOutgoing();
    exists outValues: Valuation ::
      outValues.Keys == (set formal: Parameter <- outgoing :: formal.v.name) &&
      (forall formal: Parameter <- outgoing :: HasType(outValues[formal.v.name], formal.v.typ)) &&
      (UniqueNamesImpliesUniqueOldNames(inOuts);
         FollowsFromWellFormedness(forall formal <- inOuts :: formal.v.name in entry) &&
         var oldValues := map formal <- inOuts :: OldName(formal.v.name) := entry[formal.v.name];
         exit == entry + oldValues + outValues)
  }

  predicate WriteBackOutgoingParameters(entry: Valuation, shadowedVariables: Valuation, exit: Valuation, st': State, parameters: seq<Parameter>, args: seq<CallArgument>)
    requires Stmt.MatchingParameters(parameters, args)
    requires forall formal <- parameters | formal.mode.IsOutgoing() :: formal.v.name in exit
  {
    var actualOutgoing := map i | 0 <= i < |parameters| && parameters[i].mode.IsOutgoing() :: args[i].name := exit[parameters[i].v.name];
    st' == State(entry + actualOutgoing, shadowedVariables)
  }

  greatest predicate BigStepSeq(stmts: seq<Stmt>, b3: Program, st: State, st': State)
    requires WF.StmtSeq(stmts, b3)
    requires st.State?
  {
    if stmts == [] then
      st' == st
    else
      var stmt, cont := stmts[0], stmts[1..];
      exists mid ::
        BigStep(stmt, b3, st, mid) &&
        if !mid.State? then
          st' == mid
        else
          BigStepSeq(cont, b3, mid, st')
  }

  function SeparateAssertion(stmt: Stmt, context: AssertionContext): seq<Stmt>
    requires ValidAssertionStatement(stmt)
    decreases stmt
  {
    match stmt
    case ValDecl(_, _) =>
      []
    case Check(e) =>
      [Check(context.Build(e))]
    case Assume(e) =>
      [Assume(context.Build(e))]
    case Assert(e) =>
      [Assert(context.Build(e))]
    case AForall(v, body) =>
      SeparateAssertion(body, AContextForall(v, context))
    case Block(_, stmts) =>
      SeparateAssertionSeq(stmt, stmts, context)
    case If(cond, thn, els) =>
      var s0 := SeparateAssertion(thn, AContextCondition(cond, context));
      var s1 := SeparateAssertion(els, AContextCondition(Expr.CreateNegation(cond), context));
      s0 + s1
    case IfCase(cases) =>
      var separatedCases := SeqMap(cases, (c: Case) requires c in cases => SeparateAssertion(c.body, AContextCondition(c.cond, context)));
      SeqFlatten(separatedCases)
  }

  function SeparateAssertionSeq(ghost stmt: Stmt, stmts: seq<Stmt>, context: AssertionContext): seq<Stmt>
    requires forall s <- stmts :: s < stmt && ValidAssertionStatement(s)
  {
    if stmts == [] then
      []
    else
      var s, tail := stmts[0], stmts[1..];
      assert forall s <- tail :: s in stmts;
      match s
      case ValDecl(v, rhs) =>
        SeparateAssertionSeq(stmt, tail, AContextVal(v, rhs, context))
      case _ =>
        SeparateAssertion(s, context) + SeparateAssertionSeq(stmt, tail, context)
  }

  datatype AssertionContext =
    | AContextEmpty
    | AContextForall(v: Variable, tail: AssertionContext)
    | AContextVal(v: Variable, rhs: Expr, tail: AssertionContext)
    | AContextCondition(cond: Expr, tail: AssertionContext)
  {
    function Build(e: Expr): Expr {
      match this
      case AContextEmpty => e
      case AContextForall(v, tail) =>
        tail.Build(Expr.CreateForall(v, e))
      case AContextVal(v, rhs, tail) =>
        tail.Build(Expr.CreateLet(v, rhs, e))
      case AContextCondition(cond, tail) =>
        tail.Build(Expr.CreateImplies(cond, e))
    }
  }

  // Some properties of the AST that are needed for the semantic definition are checked by well-formedness checks.
  // To obtain those properties here, well-formedness should be used as a preconditon throughout. Until that is
  // done, the FollowsFromWellFormedness predicate serves as a way to mark the necessary conditions in the source text.
  predicate FollowsFromWellFormedness(b: bool) {
    b
  }
*****/
}
