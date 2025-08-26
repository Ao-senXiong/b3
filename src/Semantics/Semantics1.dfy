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
    
    lemma IsDefinedOnTransitivity(s1: set<Variable>, s2: set<Variable>)
        requires s1 <= s2
        ensures IsDefinedOn(s1) ==> IsDefinedOn(s2)
      {  }

    // TODO: make a Dafny issue (check if there already is one)
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
      case Forall(v, body) => forall x: bool { body.EvalFVarsLemma(s1.Update(v, x), s2.Update(v, x)); }
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
    | Seq(0: Stmt, 1: Stmt)
    | Assign(lhs: Variable, rhs: Expr)
    | VarDecl(v: Variable, s: Stmt)
    // | While(guard: Expr, inv: Expr, body: Stmt)
    // | If(cond: Expr, thn: Stmt, els: Stmt)
    {
      function FVars(): set<Variable> {
        match this
        case Check(e) => e.FVars()
        case Assume(e) => e.FVars()
        case Seq(s0, s1) => s0.FVars() + s1.FVars()
        case Assign(lhs, rhs) => {lhs} + rhs.FVars()
        case VarDecl(v, s) => s.FVars() - {v}
      }

      function BVars(): set<Variable> {
        match this
        case Check(e) => e.BVars()
        case Assume(e) => e.BVars()
        case Seq(s0, s1) => s0.BVars() + s1.BVars()
        case Assign(lhs, rhs) => rhs.BVars()
        case VarDecl(v, s) => s.BVars() + {v}
      }

      predicate IsDefinedOn(s: set<Variable>) {
        FVars() <= s
      }
      lemma IsDefinedOnTransitivity(s1: set<Variable>, s2: set<Variable>)
        requires s1 <= s2
        ensures IsDefinedOn(s1) ==> IsDefinedOn(s2)
      {  }
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
    case Assign(x, v) =>
      && v.IsDefinedOn(a.Keys) 
      && z == Ok(a.Update(x, a.Eval(v)))
    case VarDecl(v, s) => exists b :: BigStep(s, a.Update(v, b), z)
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

    function FVars(): set<Variable> 
      ensures FVars() == Conj(ctx).FVars()
      ensures forall e <- ctx :: e.FVars() <= FVars()
      decreases ctx
    {
      if ctx == [] then {} else ctx[0].FVars() + Context(ctx[1..], incarnation, bVars).FVars()
    }

    ghost predicate Valid() 
    {
      && incarnation.Values <= FVars() 
      && forall b <- bVars :: b !in incarnation.Values
    }

    // How to prove that `v !in incarnation.Keys` is satisfiable?
    function FreshVar(): Variable
      ensures {:axiom} FreshVar() !in incarnation.Keys
      ensures {:axiom} FreshVar() !in bVars
      ensures {:axiom} FreshVar() !in FVars()

    // {
    //     // // assert !incarnation.Keys != {};
    //     // // assert {:axiom} exists v :: v !in incarnation.Keys;
    //     // v :| v !in incarnation.Keys by {
    //     //   // Prove existence here
    //     //   assume {:axiom} false;
    //     //   // loop increasing length
    //     // }
    // }

    function AdjustState(s: State): State
      // requires Valid()
      // requires IsDefinedOn(s.Keys)
      requires incarnation.Values <= s.Keys
    { 
      // IsDefinedOnConjLemma(ctx, s);
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

    // function SubstituteStmt(s: Stmt): Stmt 
    //   requires s.IsDefinedOn(incarnation.Keys)
    //   decreases s
    // {
    //   match s
    //   case Check(e) => Check(Substitute(e))
    //   case Assume(e) => Assume(Substitute(e))
    //   case Seq(s0, s1) => Seq(SubstituteStmt(s0), SubstituteStmt(s1))
    //   case Assign(lhs, rhs) => Assign(incarnation[lhs], Substitute(rhs))
    //   case VarDecl(v, s) => VarDecl(v, Context(ctx, incarnation[v:=v], bVars).SubstituteStmt(s))
    // }

    function MkEntailment(e: Expr): Expr 
    {
      Implies(Conj(ctx), Substitute(e))
    }


    function Add(e: Expr): Context
      requires Valid()
      ensures Valid()
      // ensures incarnation == Add(e).incarnation
      // ensures ctx <= Add(e).ctx
    {
      var ctx := ctx + [Substitute(e)];
      Context(ctx, incarnation, bVars)
    }

    method AddEq(v: Variable, e: Expr) returns (vNew: Variable, context: Context)
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
      vNew := FreshVar();
      var ctx' := ctx + [Eq(Var(vNew), Substitute(e))];
      FVarsEqLemma(Var(vNew), Substitute(e));
      FVarsConjUnionLemma(ctx, [Eq(Var(vNew), Substitute(e))]);
      var incarnation' := incarnation[v := vNew];
      context := Context(ctx', incarnation', bVars);
    }
    
    // TODO: Fix this
    // function AddVar(v: Variable): Context
    //   requires Valid()
    //   ensures AddVar(v).Valid()
    //   ensures incarnation.Keys + {v} == AddVar(v).incarnation.Keys
    //   ensures ctx == AddVar(v).ctx
    // {
    //   var vNew := FreshVar();
    //   var incarnation' := incarnation[v := vNew];
    //   Context(ctx, incarnation', bVars)
    // }
    
    // Q: why is this not working?
    ghost predicate IsDefinedOn(s: set<Variable>) 
      // ensures (forall e <- ctx :: e.IsDefinedOn(s))
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
      // requires Valid()
      requires e.IsDefinedOn(incarnation.Keys)
      // requires IsDefinedOn(s.Keys)
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
        assert forall b: bool :: AdjustState(s).Update(v, b).Eval(body) == s.Update(v, b).Eval(ctx'.Substitute(body)) by {
          forall b: bool 
            ensures AdjustState(s).Update(v, b).Eval(body) == s.Update(v, b).Eval(ctx'.Substitute(body)) {
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
              assert forall b <- body.BVars() {:trigger}, x <- incarnation[v:=v].Keys :: incarnation[v:=v][x] == b ==> x == b by {
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
      case Not(ne) => assert ne.BVars() == e.BVars();
      case And(e0, e1) => assert e0.BVars() <= e.BVars(); assert e1.BVars() <= e.BVars();
      case Or(e0, e1) => assert e0.BVars() <= e.BVars(); assert e1.BVars() <= e.BVars();
      case Implies(e0, e1) => assert e0.BVars() <= e.BVars(); assert e1.BVars() <= e.BVars();
    }

    lemma AdjustStateSubstituteLemma(s: State, e: Expr)
      requires e.BVars() <= bVars
      requires Valid()
      requires e.IsDefinedOn(incarnation.Keys)
      requires IsDefinedOn(s.Keys)
      requires incarnation.Values <= s.Keys
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

  // lemma MkEntailmentLemma(e: Expr, context: Context)
  //   requires context.Valid()
  //   ensures 
  //     context.MkEntailment(e).Holds() ==> 
  //     forall s: State :: 
  //       context.IsSatisfiedOn(s) && context.Substitute(e).IsDefinedOn(s.Keys) ==> s.Eval(context.Substitute(e)) {
  //     if context.MkEntailment(e).Holds() {
  //       forall s: State | context.IsSatisfiedOn(s) && context.Substitute(e).IsDefinedOn(s.Keys)
  //         ensures s.Eval(context.Substitute(e)) {
  //           IsDefinedOnConjLemma(context.ctx, s);
  //           context.FVarsSubsituteLemma(e);
  //           assert context.MkEntailment(e).IsDefinedOn(s.Keys);
  //           EvalConjLemma(context.ctx, s);
  //     }
  //   }
  // }

/*
  []


  x := 0
  x := 1 
  assume x == 1

  ----
  [x -> x']
  x' = 0

  x := 0
  assume x == 0
  
*/

/*
Plan for adding: 
    - VarDecl
    - If 
    - While
*/

// method VCGenAux(s: Stmt, context_in: Context, sts: set<State>, out: Except<State>) returns (result: set<Expr>, context: Context) 

lemma BigStepAssignLemma(s: State, v: Variable, x: Expr, context: Context, out: Except<State>) returns (s': State)
  requires context.IsSatisfiedOn(s)
  requires BigStep(Assign(v, x), context.AdjustState(s), out)
  ensures context.IsSatisfiedOn(s')
  ensures context.incarnation.Values <= s'.Keys
  ensures Ok(context.AdjustState(s')) == out {
    assume {:axiom} false;
  }
  

method VCGenAux(s: Stmt, context_in: Context) returns (result: set<Expr>, context: Context) 
    requires s.BVars() <= context_in.bVars
    requires s.IsDefinedOn(context_in.incarnation.Keys)

    requires context_in.Valid()
    ensures context.Valid()
    ensures context_in.bVars == context.bVars
    ensures context_in.incarnation.Keys <= context.incarnation.Keys
    ensures 
      (forall e <- result :: e.Holds()) ==> 
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
      result := {context.MkEntailment(e)};
      if context.MkEntailment(e).Holds() {
        forall st: State, out: Except<State> | context.IsSatisfiedOn(st) && BigStep(Check(e), context.AdjustState(st), out) 
           ensures out == Ok(context.AdjustState(st)) {
            assert context.AdjustState(st).Eval(e) by { 
              context.AdjustStateSubstituteLemma(st, e);
              IsDefinedOnConjLemma(context.ctx, st);
              context.SubstituteIsDefinedOnLemma(e);
              EvalConjLemma(context.ctx, st);
           }
        }
      }
    case Assume(e) =>
      context := context.Add(e);
      result := {};
      FVarsConjUnionLemma(context_in.ctx, [context_in.Substitute(e)]);
      forall st: State, out: Except<State> | context_in.IsSatisfiedOn(st) && BigStep(Assume(e), context_in.AdjustState(st), out) 
        ensures out == Ok(context.AdjustState(st))
        ensures context.IsSatisfiedOn(st)
        ensures context.incarnation.Values <= st.Keys {
        context_in.SubstituteIsDefinedOnLemma(e);
        context_in.AdjustStateSubstituteLemma(st, e); 
      }
    case Assign(v, x) =>
      var vNew;
      vNew, context := context.AddEq(v, x);
      result := {};
      forall st: State, out: Except<State> | 
        && context_in.IsSatisfiedOn(st)  
        && BigStep(Assign(v, x), context_in.AdjustState(st), out) 
        ensures (exists st': State :: 
            && context.incarnation.Values <= st'.Keys
            && Ok(context.AdjustState(st')) == out
            && context.IsSatisfiedOn(st')) {
          context_in.SubstituteIsDefinedOnLemma(x);
          var v' := st.Eval(context_in.Substitute(x));
          var st' := st.Update(vNew, v');

          context_in.SubstituteIsDefinedOnLemma(x);
          FVarsEqLemma(Var(vNew), context_in.Substitute(x));
          FVarsConjUnionLemma(context_in.ctx, [Eq(Var(vNew), context_in.Substitute(x))]);
          
          assert context.IsSatisfiedOn(st') by {
            context_in.Substitute(x).EvalFVarsLemma(st, st');
            EvalEqLemma(Var(vNew), context_in.Substitute(x), st');
            assert forall e: Expr :: e.FVars() <= context_in.FVars() ==> st.Eval(e) ==> st'.Eval(e) by {
              forall e: Expr | e.FVars() <= context_in.FVars() && st.Eval(e) { 
                e.EvalFVarsLemma(st, st');
              }
            }
          }
          assert context.AdjustState(st') == context_in.AdjustState(st).Update(v, context_in.AdjustState(st).Eval(x)) by {
              context_in.AdjustStateSubstituteLemma(st, x);
          }
        }
    case Seq(s0, s1) =>
      var res0, context' := VCGenAux(s0, context);
      var res1, context'' := VCGenAux(s1, context');
      result := res0 + res1;
      context := context'';
      if (forall e <- res0 + res1 :: e.Holds()) {
        forall st: State, out: Except<State> | context_in.IsSatisfiedOn(st) && BigStep(Seq(s0, s1), context_in.AdjustState(st), out)
          ensures (exists st': State :: 
            && context.incarnation.Values <= st'.Keys
            && Ok(context.AdjustState(st')) == out
            && context.IsSatisfiedOn(st')) {
            assert BigStep(Seq(s0, s1), context_in.AdjustState(st), out);
        }
      }
    
    case _ => assume {:axiom} false;

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