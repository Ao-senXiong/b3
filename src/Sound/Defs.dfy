module Defs { 

  ghost const AllStates: iset<State> := iset st: State | true

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

  function ExceptRemove(e: Except<State>, v: Variable): Except<State> {
    var r :- e;
    Ok(r - {v})
  }

  // import opened Values

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
      case Seq(ss) => SeqNoShadowing(ss, this)
        // && SeqNoShadowingNested(ss)
        // && (forall i, j :: 0 <= i < j < |ss| ==> ss[i].BVars() !* ss[j].BVars())
      case Assign(lhs, rhs) => rhs.NoShadowing()
      case VarDecl(v, s) => v !in s.BVars() && s.NoShadowing()
      case Choice(s0, s1) => s0.NoShadowing() && s1.NoShadowing()
    }

    predicate WellFormed() {
      NoShadowing() && FVars() !! BVars()
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

  predicate SeqIsDefinedOn(ss: seq<Stmt>, s: set<Variable>) 
    ensures SeqIsDefinedOn(ss, s) <==> SeqFVars(ss) <= s
  {
    if ss == [] then true else ss[0].IsDefinedOn(s) && SeqIsDefinedOn(ss[1..], s)
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

  predicate SeqNoShadowingNested(ss: seq<Stmt>, ghost parent: Stmt := Seq(ss)) 
    requires forall s <- ss :: s < parent
    decreases parent, |ss|
  {
    forall s <- ss :: s.NoShadowing()
  }

  predicate SeqNoShadowing(ss: seq<Stmt>, ghost parent: Stmt := Seq(ss)) 
    requires forall s <- ss :: s < parent
    decreases parent, |ss| + 1
  {
    && SeqNoShadowingNested(ss, parent)
    && (forall i, j :: 0 <= i < j < |ss| ==> ss[i].BVars() !! ss[j].BVars())
  }

  predicate SeqWellFormed(ss: seq<Stmt>) {
    if ss == [] then 
      true 
    else 
      && ss[0].WellFormed()
      && ss[0].BVars() !! SeqFVars(ss[1..]) 
      && ss[0].BVars() !! SeqBVars(ss[1..])
      && SeqWellFormed(ss[1..])
  }

  lemma SeqFunConcatLemmas(ss1: seq<Stmt>, ss2: seq<Stmt>)
    ensures SeqSize(ss1 + ss2) == SeqSize(ss1) + SeqSize(ss2)
    ensures SeqBVars(ss1 + ss2) == SeqBVars(ss1) + SeqBVars(ss2)
    ensures SeqFVars(ss1 + ss2) == SeqFVars(ss1) + SeqFVars(ss2)
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
}

