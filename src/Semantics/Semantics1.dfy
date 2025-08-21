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

    predicate IsDefinedOn(s: set<Variable>) {
      forall v <- FVars() :: v in s
    }

    // TODO: make a Dafny issue (check if there already is one)
    ghost predicate Holds() {
      forall s: State :: IsDefinedOn(s.Keys) ==> s.Eval(this)
    }
  }

  function Eq(e1: Expr, e2: Expr): Expr {
    And(Implies(e1, e2), Implies(e2, e1))
  }

  lemma FVarsEqLemma(e1: Expr, e2: Expr)
    ensures Eq(e1, e2).FVars() == e1.FVars() + e2.FVars()
  {  }
    
  datatype Stmt =
    | Check(e: Expr)
    | Assume(e: Expr)
    | Seq(0: Stmt, 1: Stmt)
    | Assign(lhs: Variable, rhs: Expr)
    // | While(guard: Expr, inv: Expr, body: Stmt)
    // | If(cond: Expr, thn: Stmt, els: Stmt)
    // | VarDecl(v: string)
    {
      function FVars(): set<Variable> {
        match this
        case Check(e) => e.FVars()
        case Assume(e) => e.FVars()
        case Seq(s0, s1) => s0.FVars() + s1.FVars()
        case Assign(lhs, rhs) => {lhs} + rhs.FVars()
      }
      predicate IsDefinedOn(s: set<Variable>) {
        forall v <- FVars() :: v in s
      }
    }

  type Value = bool

  newtype State = map<Variable, Value> {
    
  // datatype State = State(m: map<string, Value>) {
    function Eval(e: Expr): Value 
      requires e.IsDefinedOn(this.Keys)
      decreases e
    {
      match e
      case BConst(bvalue) => bvalue
      case And(e0, e1) => Eval(e0) && Eval(e1)
      case Or(e0, e1) => Eval(e0) || Eval(e1)
      case Not(e) => !Eval(e)
      case Implies(e0, e1) => !Eval(e0) || Eval(e1)
      case Forall(v, body) => forall x: bool :: Update(v, x).Eval(body)
      case Var(v) => this[v]
    }
    function Update(v: Variable, val: Value): State {
      this[v := val]
      // this.(m := m[v := val])
      // State(m[v := val])
    }
  }

  datatype Except<+T> =
    | Ok(res: T)
    | Error
  {
    predicate IsFailure() {
      Error?
    }
    function PropagateFailure<U>(f: Except<U>): Except<U>
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

  least predicate BigStep(s: Stmt, a: State, z: Except<State>) 
  {
    match s
    case Check(e) =>
      e.IsDefinedOn(a.Keys) &&
      z == if a.Eval(e) then Ok(a) else Error
    case Assume(e) =>
      e.IsDefinedOn(a.Keys) &&
      a.Eval(e) && z == Ok(a)
    case Seq(s0, s1) =>
      exists w ::
        && BigStep(s0, a, w) 
        && match w {
            case Ok(b) => 
              && s1.IsDefinedOn(b.Keys) 
              && BigStep(s1, b, z)
            case _ => z == w
        }
    case Assign(lhs, rhs) =>
      && rhs.IsDefinedOn(a.Keys) 
      && a.Eval(rhs) 
      && z == Ok(a.Update(lhs, a.Eval(rhs)))
    // case While(guard, inv, body) =>
    //   if a.Eval(guard) then
    //     BigStep(Seq(body, While(guard, inv, body)), a, z)
    // else z == Ok(a)
    // case If(cond, thn, els) =>
    //   if a.Eval(cond) then
    //     BigStep(thn, a, z)
    //   else
    //     BigStep(els, a, z)
  }

  function Conj(ctx: seq<Expr>): Expr 
  {
    if ctx == [] then BConst(true) else And(ctx[0], Conj(ctx[1..]))
  }


  lemma FVarsConjUnionLemma(ctx1: seq<Expr>, ctx2: seq<Expr>)
    ensures Conj(ctx1 + ctx2).FVars() == Conj(ctx1).FVars() + Conj(ctx2).FVars()
  {
    if ctx1 == [] {
      assert [] + ctx2 == ctx2; // if I remove this everything breaks
    } else {
      assert ctx1 + ctx2 == [ctx1[0]] + (ctx1[1..] + ctx2);
    }
  }

  // lemma FVarsConjSingleLemma(e: Expr)
  //   ensures Conj([e]).FVars() == e.FVars()
  // {  }

  class Context {
    var ctx: seq<Expr>
    var incarnation : map<Variable, Variable>

    ghost predicate Valid() 
      reads this
    {
      incarnation.Values <= Conj(ctx).FVars()
    }

    constructor () {
      ctx := [];
      incarnation := map[];
    }

    // How to prove that `v !in incarnation.Keys` is satisfiable?
    method FreshVar() returns (v: Variable) 
      ensures v !in incarnation.Keys
    {
        // assert !incarnation.Keys != {};
        // assert {:axiom} exists v :: v !in incarnation.Keys;
        v :| v !in incarnation.Keys by {
          // Prove existence here
          assume {:axiom} false;
          // loop increasing length
        }
    }

    function Substitute(e: Expr): Expr 
      reads `incarnation
    {
      match e
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
      case _ => e
    }

    function SubstituteStmt(s: Stmt): Stmt 
      requires s.IsDefinedOn(incarnation.Keys)
      reads this
    {
      match s
      case Check(e) => Check(Substitute(e))
      case Assume(e) => Assume(Substitute(e))
      case Seq(s0, s1) => Seq(SubstituteStmt(s0), SubstituteStmt(s1))
      case Assign(lhs, rhs) => Assign(incarnation[lhs], Substitute(rhs))
    }

    function MkEntailment(e: Expr): Expr 
      reads this
    {
      Implies(Conj(ctx), Substitute(e))
    }

    lemma SeqAppendLemma(x: seq<Expr>, y: seq<Expr>)
      ensures y <= x + y
    {
      if x == [] {
      } else {

      }
    }

    method Add(e: Expr) 
      requires Valid()
      ensures Valid()
      ensures incarnation == old(incarnation)
      ensures old(ctx) <= ctx
      modifies this
    {
      ctx := [Substitute(e)] + ctx;
      SeqAppendLemma([Substitute(e)], old(ctx));
    }

    method AddEq(v: Variable, e: Expr) 
      requires v in incarnation.Keys
      requires Valid()
      ensures Valid()
      ensures old(ctx) <= ctx
      ensures incarnation.Keys == old(incarnation.Keys)
      modifies this
    {
      var vNew := FreshVar();
      ctx := [Eq(Var(vNew), Substitute(e))] + ctx;
      FVarsEqLemma(Var(vNew), Substitute(e));
      incarnation := incarnation[v := vNew];
      SeqAppendLemma([Substitute(e)], old(ctx));
    }

    ghost predicate IsDefinedOn(s: set<Variable>) 
      reads this
    {
      forall e <- ctx :: e.IsDefinedOn(s)
    }

    ghost predicate IsSatisfiedOn(s: State) 
      reads this
    {
      IsDefinedOn(s.Keys) && forall e <- ctx :: s.Eval(e)
    }

    ghost predicate Entails(e: Expr) 
      reads this
    {
      forall s: State ::  
        e.IsDefinedOn(s.Keys) && IsSatisfiedOn(s) ==> s.Eval(e)
    }

  lemma FVarsSubsituteLemma(e: Expr)
    ensures Substitute(e).FVars() <= e.FVars() + incarnation.Values
  {  }
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
    // requires Conj(ctx).IsDefinedOn(s.Keys)
    requires forall e <- ctx :: e.IsDefinedOn(s.Keys)
    requires forall e <- ctx :: s.Eval(e) // 1
    ensures (IsDefinedOnConjLemma(ctx, s); s.Eval(Conj(ctx)))             // 2
  {  }

  lemma MkEntailmentLemma(e: Expr, context: Context)
    requires context.Valid()
    ensures 
      context.MkEntailment(e).Holds() ==> 
      forall s: State :: 
        context.IsSatisfiedOn(s) && context.Substitute(e).IsDefinedOn(s.Keys) ==> s.Eval(context.Substitute(e)) {
      if context.MkEntailment(e).Holds() {
        forall s: State | context.IsSatisfiedOn(s) && context.Substitute(e).IsDefinedOn(s.Keys)
          ensures s.Eval(context.Substitute(e)) {
            IsDefinedOnConjLemma(context.ctx, s);
            context.FVarsSubsituteLemma(e);
            assert context.MkEntailment(e).IsDefinedOn(s.Keys);
            EvalConjLemma(context.ctx, s);
      }
    }
  }

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
}