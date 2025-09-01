module WellFormed { 
  import opened Defs
  export 
    provides Defs
    provides SeqLemma

  predicate SeqWellFormed'(ss: seq<Stmt>) {
    && (forall s <- ss :: s.WellFormed())
    && (forall i, j :: 0 <= i < j < |ss| ==> ss[i].BVars() !! (ss[j].BVars() + ss[j].FVars()))
  }

  lemma IntersectSeqVarsLemma(s: set<Variable>, ss: seq<Stmt>)
    requires forall i :: 0 <= i < |ss| ==> s !! (ss[i].BVars() + ss[i].FVars())
    ensures s !! (SeqFVars(ss) + SeqBVars(ss))
  {  }
  lemma IntersectSeqVarsLemma'(s: set<Variable>, ss: seq<Stmt>)
    requires s !! (SeqFVars(ss) + SeqBVars(ss))
    ensures forall i :: 0 <= i < |ss| ==> s !! (ss[i].BVars() + ss[i].FVars())
  {  }

  lemma EqLemma(ss: seq<Stmt>)
    ensures SeqWellFormed'(ss) <==> SeqWellFormed(ss)
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      assert forall i :: 0 <= i < |ss[1..]| ==> ss[1..][i] == ss[i + 1];
      assert SeqWellFormed'(ss) ==> SeqWellFormed(ss) by {
        if SeqWellFormed'(ss) {
          assert ss[0].BVars() !! (SeqFVars(ss[1..]) + SeqBVars(ss[1..])) by {
            IntersectSeqVarsLemma(ss[0].BVars(), ss[1..]);
          }
        }
      }
      assert SeqWellFormed(ss) ==> SeqWellFormed'(ss) by {
        if SeqWellFormed(ss) {
          EqLemma(ss[1..]);
          IntersectSeqVarsLemma'(ss[0].BVars(), ss[1..]);
        }
      }
    }
  }

  lemma DefConsistentLemma(ss: seq<Stmt>)
    requires Seq(ss).WellFormed()
    ensures SeqWellFormed'(ss)
  { 
    assert SeqNoShadowingNested(ss) by {
      assert SeqNoShadowing(ss);
    }
    forall s | s in ss 
      ensures s.WellFormed() { 
        SeqVarsInLemma(ss, s); 
      }
    forall i, j | 0 <= i < j < |ss| 
      ensures (ss[i].BVars() !! (ss[j].BVars() + ss[j].FVars())) {
      assert ss[i].BVars() !! ss[j].FVars() by {
        SeqVarsInLemma(ss, ss[i]);
        SeqVarsInLemma(ss, ss[j]);
      }
      assert ss[i].BVars() !! ss[j].BVars() by {
        assert SeqNoShadowing(ss);
      }
    }
  }

  lemma InLemma(ss: seq<Stmt>)
    requires SeqWellFormed'(ss)
    ensures forall s <- ss :: s.WellFormed()
  {  }

  lemma SeqVarsInLemma(ss: seq<Stmt>, s: Stmt, parent: Stmt := Seq(ss))
    requires s in ss
    requires forall s <- ss :: s < parent
    ensures s.BVars() <= Seq(ss).BVars()
    ensures s.FVars() <= Seq(ss).FVars()
    ensures SeqNoShadowingNested(ss, parent) ==> s.NoShadowing()
  { 
    if ss != [] {
      if s == ss[0] {
      } else {
        assert forall s <- ss[1..] :: s in ss;
        SeqVarsInLemma(ss[1..], s, parent);
      }
    }
  }

  lemma SeqLemma'(ss: seq<Stmt>, cont: seq<Stmt>)
    requires SeqWellFormed'([Seq(ss)] + cont)
    ensures SeqWellFormed'(ss + cont)
  {
    forall s | s in ss + cont 
      ensures s.WellFormed() {
      DefConsistentLemma(ss);
      InLemma(ss);
    }
    forall i, j | 0 <= i < j < |ss + cont| 
      ensures (ss + cont)[i].BVars() !! ((ss + cont)[j].BVars() + (ss + cont)[j].FVars()) {
      if i >= |ss| {
        assert (ss + cont)[i] == ([Seq(ss)] + cont)[i - |ss| + 1];
        assert (ss + cont)[j] == ([Seq(ss)] + cont)[j - |ss| + 1];
      } else {
        if j < |ss| {
          assert (ss + cont)[i] == ss[i];
          assert (ss + cont)[j] == ss[j];
          assert ss[i].BVars() !! (ss[j].BVars() + ss[j].FVars()) by {
            DefConsistentLemma(ss);
          }
        } else {
          assert (ss + cont)[i] == ss[i];
          assert ss[i].BVars() <= Seq(ss).BVars() by {
            assert ss[i] in ss;
            SeqVarsInLemma(ss, ss[i]);
          }
          assert Seq(ss).BVars() !! (([Seq(ss)] + cont)[j - |ss| + 1].BVars() + ([Seq(ss)] + cont)[j - |ss| + 1].FVars()) by {
            assert (ss + cont)[j] == ([Seq(ss)] + cont)[j - |ss| + 1];
            assert Seq(ss) == ([Seq(ss)] + cont)[0];
          }
        }
      }
    }
  }

  lemma SeqLemma(ss: seq<Stmt>, cont: seq<Stmt>)
    requires SeqWellFormed([Seq(ss)] + cont)
    ensures SeqWellFormed(ss + cont)
  {
    forall ss { EqLemma(ss); }
    SeqLemma'(ss, cont);
  }
}