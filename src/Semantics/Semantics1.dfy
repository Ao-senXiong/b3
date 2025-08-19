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

    predicate DefinedOn(s: State) {
      forall v <- FVars() :: v in s.Keys
    }

    ghost predicate Holds() {
      forall s: State :: DefinedOn(s) ==> s.Eval(this)
    }
  }

  function Eq(e1: Expr, e2: Expr): Expr {
    And(Implies(e1, e2), Implies(e2, e1))
  }
    
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
        case Assign(lhs, rhs) => rhs.FVars()
      }
      predicate DefinedOn(s: State) {
        forall v <- FVars() :: v in s.Keys
      }
    }

  type Value = bool

  newtype State = map<Variable, Value> {
    
  // datatype State = State(m: map<string, Value>) {
    function Eval(e: Expr): Value 
      requires e.DefinedOn(this)
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
      e.DefinedOn(a) &&
      z == if a.Eval(e) then Ok(a) else Error
    case Assume(e) =>
      e.DefinedOn(a) &&
      a.Eval(e) && z == Ok(a)
    case Seq(s0, s1) =>
      exists w ::
        && BigStep(s0, a, w) 
        && match w {
            case Ok(b) => 
              && s1.DefinedOn(b) 
              && BigStep(s1, b, z)
            case _ => z == w
        }
    case Assign(lhs, rhs) =>
      && rhs.DefinedOn(a) 
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
    // Q: How to prove that `v !in incarnation.Keys` is satisfiable?
    method FreshVar() returns (v: Variable) 
      ensures {:axiom} v !in incarnation.Keys
    // {
    //     // assert !incarnation.Keys != {};
    //     // assert {:axiom} exists v :: v !in incarnation.Keys;
    //     // var u :| v !in incarnation.Keys;
    //     // v := u;
    // }

    function Substitute(e: Expr): Expr 
      reads this
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
      reads this
    {
      match s
      case Check(e) => Check(Substitute(e))
      case Assume(e) => Assume(Substitute(e))
      case Seq(s0, s1) => Seq(SubstituteStmt(s0), SubstituteStmt(s1))
      case Assign(lhs, rhs) => Assign(lhs, Substitute(rhs))
    }

    function MkEntailment(e: Expr): Expr 
      reads this
    {
      Implies(Conj(ctx), Substitute(e))
    }

    method Add(e: Expr) 
      modifies this
    {
      ctx := [Substitute(e)] + ctx;
    }

    method AddEq(v: Variable, e: Expr) 
      modifies this
    {
      var vNew := FreshVar();
      var eNew := Substitute(e);
      incarnation := incarnation[v := vNew];
      Add(Eq(Var(vNew), eNew));
    }

    ghost predicate DefinedOn(s: State) 
      reads this
    {
      forall e <- ctx :: e.DefinedOn(s)
    }

    ghost predicate IsModeled(s: State) 
      reads this
    {
      DefinedOn(s) && forall e <- ctx :: s.Eval(e)
    }

    ghost predicate Entails(e: Expr) 
      reads this
    {
      forall s: State ::  
        e.DefinedOn(s) && IsModeled(s) ==> s.Eval(e)
    }
  lemma FVarsSubsituteLemma(e: Expr)
    ensures Substitute(e).FVars() <= e.FVars() + incarnation.Values
  {  }
  }



  lemma DefinedOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.DefinedOn(s) && e1.DefinedOn(s)
    ensures And(e0, e1).DefinedOn(s) { }

  lemma DefinedOnConjLemma(ctx: seq<Expr>, s: State)
    requires forall e <- ctx :: e.DefinedOn(s)
    ensures Conj(ctx).DefinedOn(s)
    {
      if ctx != [] { DefinedOnAndLemma(ctx[0], Conj(ctx[1..]), s); }
    }

  // Q: How to get rid of one of the pre conditions?
  // they are equivalent, but one is needed for Eval in 1 and the other in 2
  lemma EvalConjLemma(ctx: seq<Expr>, s: State)
    requires Conj(ctx).DefinedOn(s)
    requires forall e <- ctx :: e.DefinedOn(s)
    requires forall e <- ctx :: s.Eval(e) // 1
    ensures s.Eval(Conj(ctx))             // 2
  {  }

  lemma MkEntailmentLemma(e: Expr, context: Context)
    requires context.Valid()
    ensures 
      context.MkEntailment(e).Holds() ==> 
      forall s: State :: 
        context.IsModeled(s) && context.Substitute(e).DefinedOn(s) ==> s.Eval(context.Substitute(e)) {
      if context.MkEntailment(e).Holds() {
        forall s: State | context.IsModeled(s) && context.Substitute(e).DefinedOn(s)
          ensures s.Eval(context.Substitute(e)) {
            DefinedOnConjLemma(context.ctx, s);
            context.FVarsSubsituteLemma(e);
            assert context.MkEntailment(e).DefinedOn(s);
            EvalConjLemma(context.ctx, s);
      }
    }
  }


  method VCGenAux(s: Stmt, context: Context) 
  returns (result: set<Expr>) 
  requires context.Valid()
  requires s.Check? || s.Assume?
  ensures context.Valid()
  ensures 
    (forall e <- result :: e.Holds()) ==> 
      forall st: State, out: Except<State> :: 
        context.IsModeled(st) ==>
        BigStep(context.SubstituteStmt(s), st, out) ==> out.Ok?
    modifies context
  {
    match s
    case Check(e) =>
      result := {context.MkEntailment(e)};
      MkEntailmentLemma(e, context);
    case Assume(e) =>
      context.Add(e);
      result := {};
    // case Seq(s0, s1) =>
    //   var r0 := VCGenAux(s0, context);
    //   var r1 := VCGenAux(s1, context);
    //   result := r0 + r1;
    // case Assign(lhs, rhs) =>
    //   context.AddEq(lhs, rhs);
    //   result := {};
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