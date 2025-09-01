module VCGenOmni {
  import opened Defs
  import opened Context
  import Omni
  import WellFormed

  ghost const AllStates: iset<State> := iset st: State | true

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
        Omni.Sem(s, context_in.AdjustState(st), context_in.AdjustedModels)
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
    case Assume(e) =>
      context := context_in.Add(e);
      VCs := [];
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
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
      case Choice(ss0, ss1) =>
        var VCs0 := SeqVCGen([ss0] + cont, context);
        var VCs1 := SeqVCGen([ss1] + cont, context);
        VCs := VCs0 + VCs1;
      case VarDecl(v, s) =>
        ghost var vNew;
        var context';
        vNew, context' := context.AddVar(v);
        VCs := SeqVCGen([s] + cont, context');
      case _ => assume {:axiom} false;
    }
  }
}