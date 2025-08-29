module Semantic { 
  import opened Values

  // class Variable
  // {
  //   const name: string

  //   constructor (name: string) {
  //     this.name := name;
  //   }
  // }
  type Variable = string

  datatype Expr =
    | BConst(bvalue: bool)
    | And(0: Expr, 1: Expr)
    | Or(0: Expr, 1: Expr)
    | Not(e: Expr)
    | Implies(0: Expr, 1: Expr)
    | Var(v: Variable)
    | Forall(v: Variable, body: Expr) 
  {
    function FVars(): set<Variable> {
      match this
      case BConst(_) => {}
      case And(e0, e1) => e0.FVars() + e1.FVars()
      case Or(e0, e1) => e0.FVars() + e1.FVars()
      case Not(e) => e.FVars()
      case Implies(e0, e1) => e0.FVars() + e1.FVars()
      case Forall(v, body) => body.FVars() - {v}
      case Var(v) => {v}
    }

    function BVars(): set<Variable> {
      match this
      case BConst(_) => {}
      case And(e0, e1) => e0.BVars() + e1.BVars()
      case Or(e0, e1) => e0.BVars() + e1.BVars()
      case Not(e) => e.BVars()
      case Implies(e0, e1) => e0.BVars() + e1.BVars()
      case Forall(v, body) => body.BVars() + {v}
      case Var(v) => {}
    }

    predicate IsDefinedOn(s: set<Variable>) {
      FVars() <= s
    }

    predicate NoShadowing() {
      match this
      case BConst(_) => true
      case Var(v) => true
      case And(e0, e1) => e0.NoShadowing() && e1.NoShadowing()
      case Or(e0, e1) => e0.NoShadowing() && e1.NoShadowing()
      case Not(e) => e.NoShadowing()
      case Implies(e0, e1) => e0.NoShadowing() && e1.NoShadowing()
      case Forall(v, body) => v !in body.BVars() && body.NoShadowing()
    }

    predicate WellFormed() {
      NoShadowing()
    }
    
    lemma IsDefinedOnTransitivity(s1: set<Variable>, s2: set<Variable>)
        requires s1 <= s2
        ensures IsDefinedOn(s1) ==> IsDefinedOn(s2)
      {  }

    ghost predicate Holds() {
      forall s: State :: IsDefinedOn(s.Keys) ==> s.Eval(this)
    }

    lemma EvalFVarsLemma(s1: State, s2: State) 
      requires IsDefinedOn(s1.Keys)
      requires IsDefinedOn(s2.Keys)
      requires forall v: Variable :: v in FVars() ==> s1[v] == s2[v]
      ensures s1.Eval(this) == s2.Eval(this)

    { 
      match this
      case Forall(v, body) => 
        forall x: bool { 
          body.EvalFVarsLemma(s1.Update(v, x), s2.Update(v, x)); 
        }
      case _ =>
    }
      
  }

  function Eq(e1: Expr, e2: Expr): Expr {
    And(Implies(e1, e2), Implies(e2, e1))
  }

  lemma FVarsEqLemma(e1: Expr, e2: Expr)
    ensures Eq(e1, e2).FVars() == e1.FVars() + e2.FVars()
  {  }

  lemma EvalEqLemma(e1: Expr, e2: Expr, s: State)
    requires e1.IsDefinedOn(s.Keys)
    requires e2.IsDefinedOn(s.Keys)
    requires s.Eval(e1) == s.Eval(e2)
    ensures s.Eval(Eq(e1, e2))
  {  }
    
  datatype Stmt =
    | Check(e: Expr)
    | Assume(e: Expr)
    | Seq(ss: seq<Stmt>)
    | Assign(lhs: Variable, rhs: Expr)
    | VarDecl(v: Variable, s: Stmt)
    // | While(guard: Expr, inv: Expr, body: Stmt)
    | Choice(0: Stmt, 1: Stmt)
  {
    function Size(): nat {
      match this
      case Check(_) => 1
      case Assume(_) => 1
      case Seq(ss) => 1 + SeqSize(ss)
      case Assign(_, _) => 1
      case Choice(s0, s1) => 1 + s0.Size() + s1.Size()
      case VarDecl(_, s) => 1 + s.Size()
    }

    function FVars(): set<Variable> {
      match this
      case Check(e) => e.FVars()
      case Assume(e) => e.FVars()
      case Seq(ss) => SeqFVars(ss)
      case Assign(lhs, rhs) => {lhs} + rhs.FVars()
      case VarDecl(v, s) => s.FVars() - {v}
      case Choice(s0, s1) => s0.FVars() + s1.FVars()
    }

    function BVars(): set<Variable> {
      match this
      case Check(e) => e.BVars()
      case Assume(e) => e.BVars()
      case Seq(ss) => SeqBVars(ss)
      case Assign(lhs, rhs) => rhs.BVars()
      case VarDecl(v, s) => s.BVars() + {v}
      case Choice(s0, s1) => s0.BVars() + s1.BVars()
    }

    predicate NoShadowing() {
      match this
      case Check(e) => e.NoShadowing()
      case Assume(e) => e.NoShadowing()
      case Seq(ss) => SeqNoShadowing(ss)
      case Assign(lhs, rhs) => rhs.NoShadowing()
      case VarDecl(v, s) => v !in s.BVars() && s.NoShadowing()
      case Choice(s0, s1) => s0.NoShadowing() && s1.NoShadowing()
    }

    predicate WellFormed() {
      NoShadowing() && (FVars() * BVars() == {})
    }

    predicate IsDefinedOn(s: set<Variable>) {
      FVars() <= s
    }
    lemma IsDefinedOnTransitivity(s1: set<Variable>, s2: set<Variable>)
      requires s1 <= s2
      ensures IsDefinedOn(s1) ==> IsDefinedOn(s2)
    {  }

    predicate Single() {
      match this
      case Assign(_, _) => true
      case Check(_) => true
      case Assume(_) => true
      case _ => false
    }
  }

  function SeqSize(ss: seq<Stmt>): nat {
    if ss == [] then 0 else ss[0].Size() + SeqSize(ss[1..])
  }

  lemma SeqSizeSplitLemma(ss: seq<Stmt>)
    requires ss != []
    ensures SeqSize(ss) == ss[0].Size() + SeqSize(ss[1..])
  {  }

  function SeqFVars(ss: seq<Stmt>): set<Variable> 
    decreases ss
  {
    if ss == [] then {} else ss[0].FVars() + SeqFVars(ss[1..])
  }

  function SeqBVars(ss: seq<Stmt>): set<Variable> {
    if ss == [] then {} else ss[0].BVars() + SeqBVars(ss[1..])
  }

  predicate SeqIsDefinedOn(ss: seq<Stmt>, s: set<Variable>) 
    ensures SeqIsDefinedOn(ss, s) <==> SeqFVars(ss) <= s
  {
    if ss == [] then true else ss[0].IsDefinedOn(s) && SeqIsDefinedOn(ss[1..], s)
  }

  predicate SeqNoShadowing(ss: seq<Stmt>) {
    if ss == [] then true else ss[0].NoShadowing() && SeqNoShadowing(ss[1..])
  }

  predicate SeqWellFormed(ss: seq<Stmt>) {
    // SeqNoShadowing(ss) && (SeqFVars(ss) * SeqBVars(ss) == {})
    if ss == [] then 
      true 
    else 
      && ss[0].WellFormed()
      && (ss[0].BVars() * SeqFVars(ss[1..]) == {}) 
      && (ss[0].BVars() * SeqBVars(ss[1..]) == {}) 
      && SeqWellFormed(ss[1..])
  }

  lemma SeqWellFormedSeqLemma(ss: seq<Stmt>, cont: seq<Stmt>)
    requires SeqWellFormed([Seq(ss)] + cont)
    ensures SeqWellFormed(ss + cont)

  lemma SeqFunConcatLemmas(ss1: seq<Stmt>, ss2: seq<Stmt>)
    ensures SeqSize(ss1 + ss2) == SeqSize(ss1) + SeqSize(ss2)
    ensures SeqBVars(ss1 + ss2) == SeqBVars(ss1) + SeqBVars(ss2)
    ensures SeqFVars(ss1 + ss2) == SeqFVars(ss1) + SeqFVars(ss2)
    ensures SeqNoShadowing(ss1 + ss2) == (SeqNoShadowing(ss1) && SeqNoShadowing(ss2))
  {
    if ss1 == [] {
      assert ss1 + ss2 == ss2;
    } else {
      assert (ss1 + ss2)[0] == ss1[0];
      assert (ss1 + ss2)[1..] == ss1[1..] + ss2;
    }
  }
    

  type Value = bool

  newtype State = map<Variable, Value> {
    
    function Eval(e: Expr): Value 
      requires e.IsDefinedOn(this.Keys)
      decreases e
    {
      match e
      case BConst(bvalue) => bvalue
      case And(e0, e1) => Eval(e0) && Eval(e1)
      case Or(e0, e1) => Eval(e0) || Eval(e1)
      case Not(e) => !Eval(e)
      case Implies(e0, e1) => Eval(e0) ==> Eval(e1)
      case Forall(v, body) => forall x: bool :: Update(v, x).Eval(body)
      case Var(v) => this[v]
    }
    function Update(v: Variable, val: Value): State {
      this[v := val]
    }
  }

  datatype Except<+T> =
    | Ok(res: T)
    | Error
  {
    predicate IsFailure() {
      Error?
    }
    function PropagateFailure<U>(): Except<U>
      requires IsFailure()
    {
      Error
    }
    function Extract() : T 
      requires !IsFailure()
    {
      res
    }
  }

  function ExceptUpdate(e: Except<State>, v: Variable, b: bool): Except<State> {
    var r :- e;
    Ok(r.Update(v, b))
  }

  least predicate BigStep[nat](s: Stmt, a: State, z: Except<State>) 
  {
    match s
    case Check(e) =>
      e.IsDefinedOn(a.Keys) &&
      z == if a.Eval(e) then Ok(a) else Error
    case Assume(e) =>
      e.IsDefinedOn(a.Keys) &&
      a.Eval(e) && z == Ok(a)
    case Seq(ss) => SeqBigStep(ss, a, z)
    case Assign(x, v) =>
      && v.IsDefinedOn(a.Keys) 
      && z == Ok(a.Update(x, a.Eval(v)))
    case VarDecl(v, s) => exists b :: 
      && BigStep(s, a.Update(v, b), ExceptUpdate(z, v, b))
      && (z.Ok? ==> v !in z.Extract().Keys)
    case Choice(s0, s1) => BigStep(s0, a, z) || BigStep(s1, a, z)
    // case While(guard, inv, body) =>
    //   if a.Eval(guard) then
    //     BigStep(Seq(body, While(guard, inv, body)), a, z)
    // else z == Ok(a)
  }

  least predicate SeqBigStep[nat](ss: seq<Stmt>, a: State, z: Except<State>) 
  {
    if ss == [] then z == Ok(a) else
      exists w ::
        && BigStep(ss[0], a, w)
        && match w {
            case Ok(b) => SeqBigStep(ss[1..], b, z)
            case _ => z == w
        }
  }

  lemma SeqBigStepConcatOkLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, st': State, out: Except<State>)
    requires SeqBigStep(ss1, st, Ok(st'))
    requires SeqBigStep(ss2, st', out)
    ensures SeqBigStep(ss1 + ss2, st, out)
  { 
    if ss1 != [] {
      var w :| BigStep(ss1[0], st, Ok(w)) && SeqBigStep(ss1[1..], w, Ok(st'));
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
    } else {
      assert [] + ss2 == ss2;
    }
  }

  lemma SeqBigStepConcatErrorLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State)
    requires SeqBigStep(ss1, st, Error)
    ensures SeqBigStep(ss1 + ss2, st, Error)
  { 
    if ss1 != [] {
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2);
      var w :| BigStep(ss1[0], st, w) && match w {
            case Ok(b) => SeqBigStep(ss1[1..], b, Error)
            case _ => Error == w };
      match w
      case Ok(st') => assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      case _ => assert (ss1 + ss2)[0] == ss1[0];
    }
  }

  lemma SeqBigStepBigStepLemma(ss: seq<Stmt>, cont: seq<Stmt>, st: State, out: Except<State>)
    requires SeqBigStep([Seq(ss)] + cont, st, out)
    ensures BigStep(Seq(ss + cont), st, out)
  {
    assert SeqBigStep(ss + cont, st, out) by {
      var w :| BigStep(Seq(ss), st, w) && match w {
            case Ok(b) => SeqBigStep(cont, b, out)
            case _ => out == w
        };
      match w
      case Ok(st') =>
        SeqBigStepConcatOkLemma(ss, cont, st, st', out);
      case _ =>
        SeqBigStepConcatErrorLemma(ss, cont, st);
    }
  } 

  lemma SeqBigStepChoiceLemma(s0: Stmt, s1: Stmt, cont: seq<Stmt>, st: State, out: Except<State>)
    requires SeqBigStep([Choice(s0, s1)] + cont, st, out)
    ensures SeqBigStep([s0] + cont, st, out) || SeqBigStep([s1] + cont, st, out)
  {
    assert forall s :: ([s] + cont)[0] == s;
    var w :| BigStep(Choice(s0, s1), st, w) && match w {
      case Ok(b) => SeqBigStep(cont, b, out)
      case _ => out == w
    };
    if BigStep(s0, st, w) {
      assert SeqBigStep([s0] + cont, st, out);
    } else {
      assert BigStep(s1, st, w);
      assert SeqBigStep([s1] + cont, st, out);
    }
  }

  lemma BigStepFrameLemma(s: Stmt, v: Variable, b: Value, st: State, out: Except<State>)
    requires BigStep(s, st, out)
    requires v !in s.FVars()
    requires v !in s.BVars()
    ensures BigStep(s, st.Update(v, b), ExceptUpdate(out, v, b))
  {
    match s
    case Assign(x, e) => 
      e.EvalFVarsLemma(st, st.Update(v, b));
      var ev := st.Eval(e);
      assert st.Update(v, b).Update(x, ev) == st.Update(x, ev).Update(v, b);
    case Check(e) => e.EvalFVarsLemma(st, st.Update(v, b));
    case Assume(e) => e.EvalFVarsLemma(st, st.Update(v, b));
    case Seq(ss) => SeqBigStepFrameLemma(ss, v, b, st, out);
    case VarDecl(u, s) =>
      var c :| 
        && BigStep(s, st.Update(u, c), ExceptUpdate(out, u, c))
        && (out.Ok? ==> u !in out.Extract().Keys);
      BigStepFrameLemma(s, v, b, st.Update(u, c), ExceptUpdate(out, u, c));
      assert st.Update(v, b).Update(u, c) == st.Update(u, c).Update(v, b);
      assert ExceptUpdate(ExceptUpdate(out, u, c), v, b) == ExceptUpdate(ExceptUpdate(out, v, b), u, c) by {
        match out
        case Ok(st') =>
          assert st'.Update(v, b).Update(u, c) == st'.Update(u, c).Update(v, b);
        case _ =>
      }
    case Choice(s0, s1) =>
  }

  lemma SeqBigStepFrameLemma(ss: seq<Stmt>, v: Variable, b: Value, st: State, out: Except<State>)
    requires SeqBigStep(ss, st, out)
    requires v !in SeqFVars(ss)
    requires v !in SeqBVars(ss)
    ensures SeqBigStep(ss, st.Update(v, b), ExceptUpdate(out, v, b))
  {
    if ss == [] {
    } else {
      var w :| BigStep(ss[0], st, w) && match w {
        case Ok(st') => SeqBigStep(ss[1..], st', out)
        case _ => out == w
      };
      BigStepFrameLemma(ss[0], v, b, st, w);
    }
  }

  function Conj(ctx: seq<Expr>): Expr 
  {
    if ctx == [] then BConst(true) else And(ctx[0], Conj(ctx[1..]))
  }

  lemma ConjFVarsMonotonicity(ctx1: seq<Expr>, ctx2: seq<Expr>)
    requires ctx1 <= ctx2
    ensures Conj(ctx1).FVars() <= Conj(ctx2).FVars()
  {  }

  lemma FVarsConjUnionLemma(ctx1: seq<Expr>, ctx2: seq<Expr>)
    ensures Conj(ctx1 + ctx2).FVars() == Conj(ctx1).FVars() + Conj(ctx2).FVars()
  {
    if ctx1 == [] {
      assert [] + ctx2 == ctx2;
    } else {
      assert ctx1 + ctx2 == [ctx1[0]] + (ctx1[1..] + ctx2);
    }
  }

  datatype Context = Context(
    ctx: seq<Expr>, 
    incarnation: map<Variable, Variable>, 
    bVars: set<Variable>) {

    function CtxFVars(): set<Variable> 
      ensures CtxFVars() == Conj(ctx).FVars()
      ensures forall e <- ctx :: e.FVars() <= CtxFVars()
      decreases ctx
    {
      if ctx == [] then {} else ctx[0].FVars() + Context(ctx[1..], incarnation, bVars).CtxFVars()
    }

    function FVars(): set<Variable> 
    {
      CtxFVars() + incarnation.Values
    }

    ghost predicate Valid() 
    {
      forall b <- bVars :: b !in incarnation.Values
    }

    function FreshVar(): Variable
      ensures {:axiom} FreshVar() !in incarnation.Keys
      ensures {:axiom} FreshVar() !in bVars
      ensures {:axiom} FreshVar() !in FVars()


    function AdjustState(s: State): State
      requires incarnation.Values <= s.Keys
    { 
      map x: Variable | x in incarnation.Keys :: s[incarnation[x]] 
    }

    function Substitute(e: Expr): Expr 
      decreases e
    {
      match e
      case BConst(bvalue) => e
      case Var(v) =>
        if v in incarnation then  
          Var(incarnation[v]) 
        else e
      case And(e0, e1) => 
        And(Substitute(e0), Substitute(e1))
      case Or(e0, e1) => 
        Or(Substitute(e0), Substitute(e1))
      case Not(e) => 
        Not(Substitute(e))
      case Implies(e0, e1) => 
        Implies(Substitute(e0), Substitute(e1))
      case Forall(v, body) => 
        Forall(v, Context(ctx, incarnation[v := v], bVars).Substitute(body))
    }

    function MkEntailment(e: Expr): Expr 
    {
      Implies(Conj(ctx), Substitute(e))
    }


    function Add(e: Expr): Context
      requires Valid()
      requires e.IsDefinedOn(incarnation.Keys)
      ensures Add(e).Valid()
    {
      ghost var ctx' := ctx;
      var ctx := ctx + [Substitute(e)];
      FVarsConjUnionLemma(ctx', [Substitute(e)]);
      Context(ctx, incarnation, bVars)
    }

    method AddEq(v: Variable, e: Expr) returns (ghost vNew: Variable, context: Context)
      requires v in incarnation.Keys
      requires Valid()
      ensures context.Valid()
      ensures incarnation.Keys == context.incarnation.Keys
      ensures ctx + [Eq(Var(vNew), Substitute(e))] == context.ctx
      ensures incarnation[v := vNew] == context.incarnation
      ensures bVars == context.bVars
      ensures vNew !in incarnation.Keys
      ensures vNew !in bVars
      ensures vNew !in FVars()
    {
      var v' := FreshVar();
      var ctx' := ctx + [Eq(Var(v'), Substitute(e))];
      FVarsEqLemma(Var(v'), Substitute(e));
      FVarsConjUnionLemma(ctx, [Eq(Var(v'), Substitute(e))]);
      var incarnation' := incarnation[v := v'];
      context := Context(ctx', incarnation', bVars);
      vNew := v';
    }
    
    // TODO: Fix this
    method AddVar(v: Variable) returns (ghost vNew: Variable, context: Context)
      requires Valid()
      ensures context.Valid()

      ensures context.incarnation == incarnation[v := vNew]
      ensures context.ctx         == ctx
      ensures context.bVars       == bVars

      ensures vNew !in incarnation.Keys
      ensures vNew !in bVars
      ensures vNew !in FVars()
    {
      var v' := FreshVar();
      var incarnation' := incarnation[v := v'];
      context := Context(ctx, incarnation', bVars);
      vNew := v';
    }
    
    ghost predicate IsDefinedOn(s: set<Variable>) 
    {
      FVars() <= s
    }

    lemma FVarsLemma(s: set<Variable>)
      requires IsDefinedOn(s)
      ensures forall e <- ctx :: e.IsDefinedOn(s)
    {  }

    ghost predicate IsSatisfiedOn(s: State) 
    {
      && IsDefinedOn(s.Keys) 
      && incarnation.Values <= s.Keys
      && forall e <- ctx :: s.Eval(e)
    }

    ghost predicate Entails(e: Expr) 
    {
      forall s: State ::  
        e.IsDefinedOn(s.Keys) && IsSatisfiedOn(s) ==> s.Eval(e)
    }

    lemma SubstituteIsDefinedOnLemma(e: Expr)
      requires e.IsDefinedOn(incarnation.Keys)
      ensures Substitute(e).IsDefinedOn(incarnation.Values)
      decreases e
    {
      assert e.FVars() <= incarnation.Keys;
      match e 
      case Forall(v, body) => Context(ctx, incarnation[v := v], bVars).SubstituteIsDefinedOnLemma(body);
      case _ => 
    }


    lemma AdjustStateSubstituteLemma'(s: State, e: Expr)
      requires forall b <- e.BVars(), x <- incarnation.Keys :: incarnation[x] == b ==> x == b
      requires e.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= s.Keys
      ensures Substitute(e).IsDefinedOn(s.Keys)
      ensures (
        SubstituteIsDefinedOnLemma(e); 
        AdjustState(s).Eval(e) == s.Eval(Substitute(e)))
      decreases e
    {
      match e 
      case Forall(v, body) => 
        var ctx' := Context(ctx, incarnation[v := v], bVars);
        SubstituteIsDefinedOnLemma(Forall(v, body)); 
        assert forall b: bool :: 
          AdjustState(s).Update(v, b).Eval(body) == 
          s.Update(v, b).Eval(ctx'.Substitute(body)) by 
        {
          forall b: bool 
            ensures AdjustState(s).Update(v, b).Eval(body) == 
              s.Update(v, b).Eval(ctx'.Substitute(body)) 
            {
              assert AdjustState(s)[v:=b] == ctx'.AdjustState(s[v:=b]) by {
                assert AdjustState(s)[v:=b].Keys == ctx'.AdjustState(s[v:=b]).Keys;
                forall x: Variable {:trigger} | x in AdjustState(s)[v:=b].Keys
                  ensures AdjustState(s)[v:=b][x] == ctx'.AdjustState(s[v:=b])[x] {
                  if x != v {
                    if incarnation[x] == v {
                      assert v in e.BVars();
                    }
                  }
                }
              }
              assert forall b <- body.BVars() {:trigger}, x <- incarnation[v:=v].Keys :: 
                incarnation[v:=v][x] == b ==> x == b by 
              {
                forall b <- body.BVars() {:trigger}, x <- incarnation[v:=v].Keys
                ensures incarnation[v:=v][x] == b ==> x == b {
                  if x != v {
                    assert e.BVars() == body.BVars() + {v};
                  }
                }
              }
            ctx'.AdjustStateSubstituteLemma'(s.Update(v, b), body);
          }
        }
      case Var(v) =>
      case BConst(bvalue) =>
      case Not(ne) => 
        assert ne.BVars() == e.BVars();
      case And(e0, e1) => 
        assert e0.BVars() <= e.BVars(); 
        assert e1.BVars() <= e.BVars();
      case Or(e0, e1) => 
        assert e0.BVars() <= e.BVars(); 
        assert e1.BVars() <= e.BVars();
      case Implies(e0, e1) => 
        assert e0.BVars() <= e.BVars(); 
        assert e1.BVars() <= e.BVars();
    }

    lemma AdjustStateSubstituteLemma(s: State, e: Expr)
      requires e.BVars() <= bVars
      requires Valid()
      requires e.IsDefinedOn(incarnation.Keys)
      requires IsDefinedOn(s.Keys)
      ensures Substitute(e).IsDefinedOn(s.Keys)
      ensures (
        SubstituteIsDefinedOnLemma(e); 
        AdjustState(s).Eval(e) == s.Eval(Substitute(e)))
    { AdjustStateSubstituteLemma'(s, e); }
  }



  lemma IsDefinedOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(s.Keys) && e1.IsDefinedOn(s.Keys)
    ensures And(e0, e1).IsDefinedOn(s.Keys) { }

  lemma IsDefinedOnConjLemma(ctx: seq<Expr>, s: State)
    requires forall e <- ctx :: e.IsDefinedOn(s.Keys)
    ensures Conj(ctx).IsDefinedOn(s.Keys)
    {
      if ctx != [] { IsDefinedOnAndLemma(ctx[0], Conj(ctx[1..]), s); }
    }

  lemma EvalConjLemma(ctx: seq<Expr>, s: State)
    requires forall e <- ctx :: e.IsDefinedOn(s.Keys)
    requires forall e <- ctx :: s.Eval(e)
    ensures (IsDefinedOnConjLemma(ctx, s); s.Eval(Conj(ctx)))
  {  }

method VCGen(s: Stmt, context_in: Context) returns (context: Context, VCs: seq<Expr>) 
  requires s.BVars() <= context_in.bVars
  requires s.IsDefinedOn(context_in.incarnation.Keys)
  requires context_in.Valid()
  requires s.Single()
  requires s.IsDefinedOn(context_in.incarnation.Keys)

  ensures context.Valid()
  ensures context_in.bVars == context.bVars
  ensures context_in.incarnation.Keys <= context.incarnation.Keys
  ensures (forall e <- VCs :: e.Holds()) ==> 
    forall st: State, out: Except<State> :: 
      context_in.IsSatisfiedOn(st) ==>
      BigStep(s, context_in.AdjustState(st), out) ==>
      exists st': State :: 
        && context.incarnation.Values <= st'.Keys
        && Ok(context.AdjustState(st')) == out
        && context.IsSatisfiedOn(st')
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
      if context.MkEntailment(e).Holds() {
        forall st: State, out: Except<State> | 
        context.IsSatisfiedOn(st) && BigStep(Check(e), context.AdjustState(st), out) 
           ensures out == Ok(context.AdjustState(st)) 
        {
          assert context.AdjustState(st).Eval(e) by { 
            context.AdjustStateSubstituteLemma(st, e);
            IsDefinedOnConjLemma(context.ctx, st);
            context.SubstituteIsDefinedOnLemma(e);
            EvalConjLemma(context.ctx, st);
          }
        }
      }
    case Assume(e) =>
      context := context_in.Add(e);
      VCs := [];
      FVarsConjUnionLemma(context_in.ctx, [context_in.Substitute(e)]);
      forall st: State, out: Except<State> | 
        context_in.IsSatisfiedOn(st) && BigStep(Assume(e), context_in.AdjustState(st), out) 
        ensures out == Ok(context.AdjustState(st))
        ensures context.IsSatisfiedOn(st)
        ensures context.incarnation.Values <= st.Keys 
      {
        context_in.SubstituteIsDefinedOnLemma(e);
        context_in.AdjustStateSubstituteLemma(st, e); 
      }
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
      forall st: State, out: Except<State> | 
        && context_in.IsSatisfiedOn(st)  
        && BigStep(Assign(v, x), context_in.AdjustState(st), out) 
        ensures (exists st': State :: 
            && context.incarnation.Values <= st'.Keys
            && Ok(context.AdjustState(st')) == out
            && context.IsSatisfiedOn(st')) 
      {
        context_in.SubstituteIsDefinedOnLemma(x);
        var v' := st.Eval(context_in.Substitute(x));
        var st' := st.Update(vNew, v');

        context_in.SubstituteIsDefinedOnLemma(x);
        FVarsEqLemma(Var(vNew), context_in.Substitute(x));
        FVarsConjUnionLemma(context_in.ctx, [Eq(Var(vNew), context_in.Substitute(x))]);
        
        assert context.IsSatisfiedOn(st') by {
          context_in.Substitute(x).EvalFVarsLemma(st, st');
          EvalEqLemma(Var(vNew), context_in.Substitute(x), st');
          assert forall e: Expr :: e.FVars() <= context_in.FVars() ==> 
            st.Eval(e) ==> st'.Eval(e) by 
          {
            forall e: Expr | e.FVars() <= context_in.FVars() && st.Eval(e) { 
              e.EvalFVarsLemma(st, st');
            }
          }
        }
        assert context.AdjustState(st') == 
          context_in.AdjustState(st).Update(v, context_in.AdjustState(st).Eval(x)) by 
        {
            context_in.AdjustStateSubstituteLemma(st, x);
        }
      }
    case _ => assume {:axiom} false;
  }

method SeqVCGen(s: seq<Stmt>, context_in: Context) returns (context: Context, VCs: seq<Expr>) 
    requires SeqWellFormed(s)
    requires SeqBVars(s) <= context_in.bVars
    requires SeqIsDefinedOn(s, context_in.incarnation.Keys)

    requires context_in.Valid()
    ensures context.Valid()
    ensures context_in.bVars == context.bVars
    ensures context_in.incarnation.Keys <= context.incarnation.Keys
    decreases SeqSize(s)
    ensures
      (forall e <- VCs :: e.Holds()) ==> 
        forall st: State, out: Except<State> :: 
          context_in.IsSatisfiedOn(st) ==>
          SeqBigStep(s, context_in.AdjustState(st), out) ==> out.Ok?
  {
    context := context_in;
    if s == [] { 
      VCs := []; 
      return; 
    }

    var stmt, cont := s[0], s[1..];
    assert s == [stmt] + cont;
    SeqSizeSplitLemma(s);
    if stmt.Single() {
      var VCstmt, VCcont;
      context, VCstmt := VCGen(stmt, context);
      context, VCcont := SeqVCGen(cont, context);
      VCs := VCstmt + VCcont;
    } else {
      match stmt 
      case Seq(ss) =>
        SeqFunConcatLemmas(ss, cont);
        SeqWellFormedSeqLemma(ss, cont);
        context, VCs := SeqVCGen(ss + cont, context);
        if (forall e <- VCs :: e.Holds()) {
          forall st: State, out: Except<State> | context_in.IsSatisfiedOn(st) && SeqBigStep(s, context_in.AdjustState(st), out) 
            ensures out.Ok?
          {
            assert BigStep(Seq(ss + cont), context_in.AdjustState(st), out) by {
              SeqBigStepBigStepLemma(ss, cont, context_in.AdjustState(st), out);
            }
          }
        }
      case Choice(ss0, ss1) =>
        var context0, VCs0 := SeqVCGen([ss0] + cont, context);
        var context1, VCs1 := SeqVCGen([ss1] + cont, context);
        context := context1;
        VCs := VCs0 + VCs1;
        if (forall e <- VCs :: e.Holds()) {
          forall st: State, out: Except<State> | 
            && context_in.IsSatisfiedOn(st)  
            && SeqBigStep([Choice(ss0, ss1)] + cont, context_in.AdjustState(st), out) 
            ensures out.Ok?
          {
            assert || SeqBigStep([ss0] + cont, context_in.AdjustState(st), out) 
                   || SeqBigStep([ss1] + cont, context_in.AdjustState(st), out) by
            {
              SeqBigStepChoiceLemma(ss0, ss1, cont, context_in.AdjustState(st), out);
            }
          }
        }
      case VarDecl(v, s) =>
        ghost var vNew;
        var context';
        vNew, context' := context.AddVar(v);
        context, VCs := SeqVCGen([s] + cont, context');
        if (forall e <- VCs :: e.Holds()) { 
          forall st: State, out: Except<State> | 
            && context_in.IsSatisfiedOn(st)  
            && SeqBigStep([stmt] + cont, context_in.AdjustState(st), out) 
            ensures out.Ok?
          { 
            var w :| BigStep(VarDecl(v, s), context_in.AdjustState(st), w) && match w {
              case Ok(st') => SeqBigStep(cont, st', out)
              case _ => out == w
            } by {
              assert SeqBigStep([stmt] + cont, context_in.AdjustState(st), out);
            }
            var b :| BigStep(s, context_in.AdjustState(st).Update(v,b), ExceptUpdate(w, v, b));
            assert context_in.AdjustState(st).Update(v,b) == context'.AdjustState(st.Update(vNew, b));
            assert context'.IsSatisfiedOn(st.Update(vNew, b)) by {
              forall e <- context'.ctx 
                ensures st.Update(vNew, b).Eval(e) {
                e.EvalFVarsLemma(st, st.Update(vNew, b));
              }
            }
            assert SeqBigStep([s] + cont, context'.AdjustState(st.Update(vNew, b)), ExceptUpdate(out, v, b)) by {
              assert BigStep(s, context'.AdjustState(st.Update(vNew, b)), ExceptUpdate(w, v, b));
              match w 
              case Ok(st') => 
                SeqBigStepFrameLemma(cont, v, b, st', out);
              case _ => 
            }
          }
        }
      case _ => assume {:axiom} false;
    }
    // match stmt
    // case Check(e) =>
    //   var VC := context.MkEntailment(e);
    //   context, VCs := SeqVCGen(cont, context);
    //   VCs := [VC] + VCs;
      // if context.MkEntailment(e).Holds() {
      //   forall st: State, out: Except<State> | context.IsSatisfiedOn(st) && BigStep(Check(e), context.AdjustState(st), out) 
      //      ensures out == Ok(context.AdjustState(st)) {
      //       assert context.AdjustState(st).Eval(e) by { 
      //         context.AdjustStateSubstituteLemma(st, e);
      //         IsDefinedOnConjLemma(context.ctx, st);
      //         context.SubstituteIsDefinedOnLemma(e);
      //         EvalConjLemma(context.ctx, st);
      //      }
      //   }
      // }
    // case Assume(e) =>
    //   context := context.Add(e);
    //   context, VCs := SeqVCGen(cont, context);
      // FVarsConjUnionLemma(context_in.ctx, [context_in.Substitute(e)]);
      // forall st: State, out: Except<State> | context_in.IsSatisfiedOn(st) && BigStep(Assume(e), context_in.AdjustState(st), out) 
      //   ensures out == Ok(context.AdjustState(st))
      //   ensures context.IsSatisfiedOn(st)
      //   ensures context.incarnation.Values <= st.Keys {
      //   context_in.SubstituteIsDefinedOnLemma(e);
      //   context_in.AdjustStateSubstituteLemma(st, e); 
      // }
    // case Assign(v, x) =>
    //   var vNew;
    //   vNew, context := context.AddEq(v, x);
    //   context, VCs := SeqVCGen(cont, context);
      // forall st: State, out: Except<State> | 
      //   && context_in.IsSatisfiedOn(st)  
      //   && BigStep(Assign(v, x), context_in.AdjustState(st), out) 
      //   ensures (exists st': State :: 
      //       && context.incarnation.Values <= st'.Keys
      //       && Ok(context.AdjustState(st')) == out
      //       && context.IsSatisfiedOn(st')) {
      //     context_in.SubstituteIsDefinedOnLemma(x);
      //     var v' := st.Eval(context_in.Substitute(x));
      //     var st' := st.Update(vNew, v');

      //     context_in.SubstituteIsDefinedOnLemma(x);
      //     FVarsEqLemma(Var(vNew), context_in.Substitute(x));
      //     FVarsConjUnionLemma(context_in.ctx, [Eq(Var(vNew), context_in.Substitute(x))]);
          
      //     assert context.IsSatisfiedOn(st') by {
      //       context_in.Substitute(x).EvalFVarsLemma(st, st');
      //       EvalEqLemma(Var(vNew), context_in.Substitute(x), st');
      //       assert forall e: Expr :: e.FVars() <= context_in.FVars() ==> st.Eval(e) ==> st'.Eval(e) by {
      //         forall e: Expr | e.FVars() <= context_in.FVars() && st.Eval(e) { 
      //           e.EvalFVarsLemma(st, st');
      //         }
      //       }
      //     }
      //     assert context.AdjustState(st') == context_in.AdjustState(st).Update(v, context_in.AdjustState(st).Eval(x)) by {
      //         context_in.AdjustStateSubstituteLemma(st, x);
      //     }
      //   }
    // case Seq(ss) =>
    //   SeqSizeConcatLemma(ss, cont);
    //   SeqFVarsConcatLemma(ss, cont);
    //   SeqBVarsConcatLemma(ss, cont);
    //   context, VCs := SeqVCGen(ss + cont, context);
      // if (forall e <- res0 + res1 :: e.Holds()) {
      //   forall st: State, out: Except<State> | context_in.IsSatisfiedOn(st) && BigStep(Seq(s0, s1), context_in.AdjustState(st), out)
      //     ensures (exists st': State :: 
      //       && context.incarnation.Values <= st'.Keys
      //       && Ok(context.AdjustState(st')) == out
      //       && context.IsSatisfiedOn(st')) {
      //       assert BigStep(Seq(s0, s1), context_in.AdjustState(st), out);
      //   }
      // }
    // case If(cond, thn, els) =>
    //   var contextForThn := context.Add(cond);
    //   var contextForEls := context.Add(Not(cond));
    //   var res0, _ 
    // case _ => assume {:axiom} false;

    // case While(guard, inv, body) =>
    //   var invIn := context.MkEntailment(inv);

      // var ctxInv := new Context();
      // ctxInv.Add(inv);

      // var invMid := VCGenAux(body, ctxInv);
      // var invPreserve := ctxInv.MkEntailment(inv);
      // result := {invIn} + invMid + {invPreserve};
      
    // case If(cond, thn, els) => result := {BConst(false)}; // what happens here?
      // var ctx := context;
      // var r0 := VCGenAux(thn, ctx);
      // var r1 := VCGenAux(els, ctx);
      // result := r0 + r1;
  }
}
/*
  method VCGenAux(s: Stmt, context: Context) returns (result: set<Expr>) 
    requires context.Valid()
    requires s.IsDefinedOn(context.incarnation.Keys)
    ensures context.Valid()
    ensures old(context.incarnation.Keys) == context.incarnation.Keys
    ensures old(context.ctx) <= context.ctx
    ensures 
      (forall e <- result :: e.Holds()) ==> 
        forall st: State, out: Except<State> :: 
          // Q: why old(context).IsSatisfiedOn(st) does not work?
          old(context.IsSatisfiedOn(st)) ==>
          BigStep(old(context.SubstituteStmt(s)), st, out) ==> out.Ok?
    modifies context
  {
    match s
    case Check(e) =>
      result := {context.MkEntailment(e)};
      MkEntailmentLemma(e, context);
    case Assume(e) =>
      context.Add(e);
      result := {};
    case Assign(lhs, rhs) =>
      context.AddEq(lhs, rhs);
      result := {};
    case Seq(s0, s1) =>
      // assume {:axiom} false;
      var r0 := VCGenAux(s0, context);
      ghost var ctx := context.ctx;
      var r1 := VCGenAux(s1, context);
      assert ctx <= context.ctx;
      assert 
        (forall e <- r0 :: e.Holds()) ==> 
          forall st: State, out: Except<State> :: 
            old(context.IsSatisfiedOn(st)) ==>
            BigStep(old(context.SubstituteStmt(s0)), st, out) ==> out.Ok?;
      assert 
        (forall e <- r0 :: e.Holds()) ==> 
          forall st: State, out: Except<State> :: 
            old(context.IsSatisfiedOn(st)) ==>
            BigStep(old(context.SubstituteStmt(s0)), st, out) ==> out.Ok?;
      result := r0 + r1;
    // case While(guard, inv, body) =>
    //   var invIn := context.MkEntailment(inv);

      // var ctxInv := new Context();
      // ctxInv.Add(inv);

      // var invMid := VCGenAux(body, ctxInv);
      // var invPreserve := ctxInv.MkEntailment(inv);
      // result := {invIn} + invMid + {invPreserve};
      
    // case If(cond, thn, els) => result := {BConst(false)}; // what happens here?
      // var ctx := context;
      // var r0 := VCGenAux(thn, ctx);
      // var r1 := VCGenAux(els, ctx);
      // result := r0 + r1;
  }
}*/