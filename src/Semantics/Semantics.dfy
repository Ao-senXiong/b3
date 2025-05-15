// TODO: calls, enclosing procedures, auto-invariants

module Semantics {
  import opened Basics
  import opened Ast
  import opened Values

  // Big-step semantics

  datatype State =
    | State(m: Valuation)
    | AbruptExit(lbl: string, m: Valuation)
    | Error
  {
    function Update(name: string, val: Value): State
      requires State?
    {
      State(m[name := val])
    }
    function Raise(lbl: string): State
      requires State?
    {
      AbruptExit(lbl, m)
    }
    function Lower(lbl: string): State {
      if AbruptExit? && lbl == this.lbl then State(m) else this
    }
    function RestoreScope(orig: State): State
      requires orig.State?
    {
      match this
      case State(m) => this.(m := MapProject(m, orig.m.Keys))
      case AbruptExit(_, m) => this.(m := MapProject(m, orig.m.Keys))
      case Error => Error
    }
  }

  // In a program `b3`, the judgement `BigStep(stmt, b3, st, st')` says that it's
  // possible to start `stmt` is state `st` and either not terminate at all or terminate
  // in state `st'`.
  greatest predicate BigStep(stmt: Stmt, b3: Program, st: State, st': State)
    requires st.State?
  {
    match stmt
    case VarDecl(v) =>
      exists val :: HasType(val, v.typ) && st' == st.Update(v.name, val)
    case ValDecl(v, rhs) =>
      st' == st.Update(v.name, rhs.Eval(st.m))
    case Assign(lhs, rhs) =>
      st' == st.Update(lhs, rhs.Eval(st.m))
    case Block(lbl, stmts) =>
      exists mid :: BigStepList(stmts, b3, st, mid) && st' == mid.Lower(lbl).RestoreScope(st)
    case Call(name, args) =>
      exists proc <- b3.procedures | proc.name == name ::
        FollowsFromWellFormedness(Stmt.MatchingParameters(proc.parameters, args) && Variable.UniqueNames(proc.parameters)) &&
        exists entry | ProcEntryParameters(st.m, entry, proc.parameters, args) ::
          exists st0 | BigStepList(proc.pre.Map((ae: AExpr) => ae.ToCheckStmt()), b3, State(entry), st0) ::
            || (!st0.State? && st' == st0)
            || (st0.State? &&
                exists exit | ProcExitParameters(entry, exit, proc.parameters, args) ::
                  exists st1 | BigStepList(proc.post.Map((ae: AExpr) => ae.ToAssumeStmt()), b3, State(exit), st1) ::
                    WriteBackOutgoingParameters(st, st1, st', proc.parameters, args))
    case Check(cond) =>
      if cond.Eval(st.m) == True then st' == st else st' == Error
    case Assume(cond) =>
      cond.Eval(st.m) == True && st' == st
    case Assert(cond) =>
      if cond.Eval(st.m) == True then st' == st else st' == Error
    case AForall(v, body) =>
      true
      /*
      // TODO: This needs to be revised. For example, `forall x: int { assume x == 2 }` should have the effect of `assume false`.
      //       So, need to `assume forall v :: Learn[[ body ]]`.
      //       Also, the `end` is wrong, because of it is `Error`, then `st'` should also be `Error`.
      // It seems the whole AForall statement needs to be converted into a sequences of quantified check/assume/assert's.
      && (exists end :: BigStep(body, b3, st, end))
      && st' == st
      */
    case If(cond, thn, els) =>
      BigStep(if cond.Eval(st.m) == True then thn else els, b3, st, st')
    case IfCase(cases) =>
      exists cs <- cases :: cs.cond.Eval(st.m) == True && BigStep(cs.body, b3, st, st')
    case Loop(lbl, invariants, body) =>
      exists st0 ::
        BigStepList(invariants.Map((ae: AExpr) => ae.ToCheckStmt()), b3, st, st0) &&
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

  ghost predicate ProcEntryParameters(callState: Valuation, entry: Valuation, parameters: seq<Variable>, args: seq<CallArgument>)
    requires Stmt.MatchingParameters(parameters, args) && Variable.UniqueNames(parameters)
  {
    FollowsFromWellFormedness(forall arg <- args :: arg.ArgLValue? ==> arg.name in callState) &&
    entry == map i | 0 <= i < |args| && parameters[i].kind.IsIncomingParameter() :: parameters[i].name := args[i].Eval(callState)
  }

  ghost predicate ProcExitParameters(entry: Valuation, exit: Valuation, parameters: seq<Variable>, args: seq<CallArgument>)
    requires Variable.UniqueNames(parameters)
  {
    var inOuts := set formal <- parameters | formal.kind == InOut;
    var outgoing := set formal <- parameters | formal.kind.IsOutgoingParameter();
    exists outValues: Valuation ::
      outValues.Keys == (set formal: Variable <- outgoing :: formal.name) &&
      (forall formal: Variable <- outgoing :: HasType(outValues[formal.name], formal.typ)) &&
      (UniqueNamesImpliesUniqueOldNames(inOuts);
        FollowsFromWellFormedness(forall formal <- inOuts :: formal.name in entry) &&
        var oldValues := map formal <- inOuts :: OldName(formal.name) := entry[formal.name];
        exit == entry + oldValues + outValues)
  }

  predicate WriteBackOutgoingParameters(st: State, exit: State, st': State, parameters: seq<Variable>, args: seq<CallArgument>) {
    true // TODO
  }

  greatest predicate BigStepList(stmts: List<Stmt>, b3: Program, st: State, st': State)
    requires st.State?
  {
    match stmts
    case Nil => st' == st
    case Cons(stmt, cont) =>
      exists mid ::
        BigStep(stmt, b3, st, mid) &&
        if !mid.State? then
          st' == mid
        else
          BigStepList(cont, b3, mid, st')
  }

  // Some properties of the AST that are needed for the semantic definition are checked by well-formedness checks.
  // To obtain those properties here, well-formedness should be used as a preconditon throughout. Until that is
  // done, the FollowsFromWellFormedness predicate serves as a way to mark the necessary conditions in the source text.
  predicate FollowsFromWellFormedness(b: bool) {
    b
  }
}
