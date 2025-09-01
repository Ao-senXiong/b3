module Context {
  import opened Defs

  datatype Context = Context(
    ctx: seq<Expr>, 
    incarnation: map<Variable, Variable>, 
    bVars: set<Variable>) 
  {

    ghost const Models : iset<State> := iset st: State | IsSatisfiedOn(st)
    // Q: is it correct way to set a trigger?
    ghost const AdjustedModels : iset<State> := iset st: State | exists st' <- Models {:InAdjustedModelsLemma(st')} :: AdjustState(st') == st

    lemma InAdjustedModelsLemma(st: State, st': State)
      requires IsSatisfiedOn(st')
      requires st == AdjustState(st')
      ensures st in AdjustedModels
    {

    }

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

}