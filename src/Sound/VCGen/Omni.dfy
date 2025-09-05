/*module VCGenOmni {
  import opened Defs
  import opened Context
  import Omni
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
      forall st: State :: 
        context_in.IsSatisfiedOn(st) ==>
        Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels)
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
      if (forall e <- VCs :: e.Holds()) {
        assert context.MkEntailment(e).Holds();
        forall st: State | context.IsSatisfiedOn(st) 
          ensures Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels) {
          assert context.AdjustState(st).Eval(e) by { 
            context.AdjustStateSubstituteLemma(st, e);
            EvalConjLemma(context.ctx, st);
          }
        }
      }
    case Assume(e) =>
      context := context_in.Add(e);
      VCs := [];
      forall st: State | context_in.IsSatisfiedOn(st) 
        ensures Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels) {
        if context.AdjustState(st).Eval(e) {
          context_in.SubstituteIsDefinedOnLemma(e);
          context_in.AdjustStateSubstituteLemma(st, e);
          FVarsConjUnionLemma(context_in.ctx, [context_in.Substitute(e)]);
        }
      }
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
      forall st: State | context_in.IsSatisfiedOn(st) 
        ensures Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels) {
        context_in.SubstituteIsDefinedOnLemma(x);
        var v' := st.Eval(context_in.Substitute(x));
        var st' := st.Update(vNew, v');
        var stTransformed := context_in.AdjustState(st).Update(v, context_in.AdjustState(st).Eval(x));

        assert stTransformed == context.AdjustState(st') by {
          context_in.AdjustStateSubstituteLemma(st, x);
        }

        assert context.IsSatisfiedOn(st') by {
          context_in.SubstituteIsDefinedOnLemma(x);
          FVarsEqLemma(Var(vNew), context_in.Substitute(x));
          FVarsConjUnionLemma(context_in.ctx, [Eq(Var(vNew), context_in.Substitute(x))]);

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
      forall st: State:: 
        context.IsSatisfiedOn(st) ==> Omni.SeqSem(s, context.AdjustState(st), AllStates)
  {
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
          forall st: State | context.IsSatisfiedOn(st) {
            Omni.SeqLemma(ss, cont, context.AdjustState(st), AllStates);
          }
        }
      case Choice(ss0, ss1) =>
        var VCs0 := SeqVCGen([ss0] + cont, context);
        var VCs1 := SeqVCGen([ss1] + cont, context);
        VCs := VCs0 + VCs1;
      case VarDecl(v, s) =>
        ghost var vNew;
        var context';
        vNew, context' := context.AddVar(v);
        VCs := SeqVCGen([s] + cont, context');
        if (forall e <- VCs :: e.Holds()) {
          forall st: State | context.IsSatisfiedOn(st)
            ensures Omni.SeqSem([VarDecl(v, s)] + cont, context.AdjustState(st), AllStates) {
            Omni.SemNest(VarDecl(v, s), cont, context.AdjustState(st), AllStates) by {
              forall b: Value ensures Omni.Sem(s, context.AdjustState(st).Update(v, b), 
                UpdateSet(v, Omni.SeqWP(cont, AllStates)))
              {
                assert context.AdjustState(st).Update(v,b) == context'.AdjustState(st.Update(vNew, b));
                assert context'.IsSatisfiedOn(st.Update(vNew, b)) by {
                  forall e <- context'.ctx 
                    ensures st.Update(vNew, b).Eval(e) {
                    e.EvalFVarsLemma(st, st.Update(vNew, b));
                  }
                }
                Omni.SemCons(s, context.AdjustState(st).Update(v, b), 
                  Omni.SeqWP(cont, AllStates), 
                  UpdateSet(v, Omni.SeqWP(cont, AllStates))) by 
                {
                  forall st | Omni.SeqSem(cont, st, AllStates) 
                    ensures Omni.SeqSem(cont, st - {v}, AllStates) {
                    Omni.SeqFrameLemmaAll(cont, v, st);
                  }
                }
              }
            }
          }
        }
    }
  }
}*/