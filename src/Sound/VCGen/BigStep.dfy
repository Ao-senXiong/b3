module VCGenBigStep {
  import opened Defs
  import opened Context
  import BigStep
  import WellFormed
  

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
        BigStep.Sem(s, context_in.AdjustState(st), out) ==>
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
        context.IsSatisfiedOn(st) && BigStep.Sem(Check(e), context.AdjustState(st), out) 
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
      forall st: State, out: Except<State> | 
        && context_in.IsSatisfiedOn(st)
        && BigStep.Sem(Assume(e), context_in.AdjustState(st), out)
        ensures out == Ok(context.AdjustState(st))
        ensures context.IsSatisfiedOn(st)
        ensures context.incarnation.Values <= st.Keys 
      {
        context_in.SubstituteIsDefinedOnLemma(e);
        context_in.AdjustStateSubstituteLemma(st, e); 
        FVarsConjUnionLemma(context_in.ctx, [context_in.Substitute(e)]);
      }
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
      forall st: State, out: Except<State> | 
        && context_in.IsSatisfiedOn(st)  
        && BigStep.Sem(Assign(v, x), context_in.AdjustState(st), out) 
        ensures (exists st': State :: 
            && context.incarnation.Values <= st'.Keys
            && Ok(context.AdjustState(st')) == out
            && context.IsSatisfiedOn(st')) 
      {
        context_in.SubstituteIsDefinedOnLemma(x);
        var v' := st.Eval(context_in.Substitute(x));
        var st' := st.Update(vNew, v');
        var stTransformed := context_in.AdjustState(st).Update(v, context_in.AdjustState(st).Eval(x));

        context_in.SubstituteIsDefinedOnLemma(x);
        FVarsEqLemma(Var(vNew), context_in.Substitute(x));
        FVarsConjUnionLemma(context_in.ctx, [Eq(Var(vNew), context_in.Substitute(x))]);

        assert context.AdjustState(st') == stTransformed by {
          context_in.AdjustStateSubstituteLemma(st, x);
        }
        
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
      }
  }

  method SeqVCGen(s: seq<Stmt>, context: Context) returns (VCs: seq<Expr>) 
    requires SeqWellFormed(s)
    requires SeqBVars(s) <= context.bVars
    requires SeqIsDefinedOn(s, context.incarnation.Keys)

    requires context.Valid()
    decreases SeqSize(s)
    ensures
      (forall e <- VCs :: e.Holds()) ==> 
        forall st: State, out: Except<State> :: 
          context.IsSatisfiedOn(st) ==>
          BigStep.SeqSem(s, context.AdjustState(st), out) ==> out.Ok?
  {
    // context := context_in;
    if s == [] { 
      VCs := []; 
      return; 
    }

    var stmt, cont := s[0], s[1..];
    assert s == [stmt] + cont;
    SeqSizeSplitLemma(s);
    if stmt.Single() {
      var VCstmt, VCcont, context';
      context', VCstmt := VCGen(stmt, context);
      VCcont := SeqVCGen(cont, context');
      VCs := VCstmt + VCcont;
    } else {
      match stmt 
      case Seq(ss) =>
        SeqFunConcatLemmas(ss, cont);
        WellFormed.SeqLemma(ss, cont);
        VCs := SeqVCGen(ss + cont, context);
        if (forall e <- VCs :: e.Holds()) {
          forall st: State, out: Except<State> | context.IsSatisfiedOn(st) && BigStep.SeqSem(s, context.AdjustState(st), out) 
            ensures out.Ok?
          {
            assert BigStep.Sem(Seq(ss + cont), context.AdjustState(st), out) by {
              BigStep.SeqLemma(ss, cont, context.AdjustState(st), out);
            }
          }
        }
      case Choice(ss0, ss1) =>
        var VCs0 := SeqVCGen([ss0] + cont, context);
        var VCs1 := SeqVCGen([ss1] + cont, context);
        VCs := VCs0 + VCs1;
        if (forall e <- VCs :: e.Holds()) {
          forall st: State, out: Except<State> | 
            && context.IsSatisfiedOn(st)  
            && BigStep.SeqSem([Choice(ss0, ss1)] + cont, context.AdjustState(st), out) 
            ensures out.Ok?
          {
            assert || BigStep.SeqSem([ss0] + cont, context.AdjustState(st), out) 
                   || BigStep.SeqSem([ss1] + cont, context.AdjustState(st), out) by
            {
              BigStep.SeqChoiceLemma(ss0, ss1, cont, context.AdjustState(st), out);
            }
          }
        }
      case VarDecl(v, s) =>
        ghost var vNew;
        var context';
        vNew, context' := context.AddVar(v);
        VCs := SeqVCGen([s] + cont, context');
        if (forall e <- VCs :: e.Holds()) { 
          forall st: State, out: Except<State> | 
            && context.IsSatisfiedOn(st)  
            && BigStep.SeqSem([stmt] + cont, context.AdjustState(st), out) 
            ensures out.Ok?
          { 
            var w :| BigStep.Sem(VarDecl(v, s), context.AdjustState(st), w) && match w {
              case Ok(st') => BigStep.SeqSem(cont, st', out)
              case _ => out == w
            } by {
              assert BigStep.SeqSem([stmt] + cont, context.AdjustState(st), out);
            }
            var b :| BigStep.Sem(s, context.AdjustState(st).Update(v,b), ExceptUpdate(w, v, b));
            assert context.AdjustState(st).Update(v,b) == context'.AdjustState(st.Update(vNew, b));
            assert context'.IsSatisfiedOn(st.Update(vNew, b)) by {
              forall e <- context'.ctx 
                ensures st.Update(vNew, b).Eval(e) {
                e.EvalFVarsLemma(st, st.Update(vNew, b));
              }
            }
            assert BigStep.SeqSem([s] + cont, context'.AdjustState(st.Update(vNew, b)), ExceptUpdate(out, v, b)) by {
              assert BigStep.Sem(s, context'.AdjustState(st.Update(vNew, b)), ExceptUpdate(w, v, b));
              match w 
              case Ok(st') => 
                BigStep.SeqFrameLemma(cont, v, b, st', out);
              case _ => 
            }
          }
        }
    }
  }
}