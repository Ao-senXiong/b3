module Omni {
  import opened Defs
  export
    provides Defs, SeqLemma, SeqChoiceLemma
    reveals Sem, SeqSem, VarDeclWitness


  least predicate VarDeclWitness(st: State, v: Variable, post: iset<State>) {
    st - {v} in post
  }

  least predicate Sem(s: Stmt, st: State, post: iset<State>) {
    match s
    case Check(e)       => e.IsDefinedOn(st.Keys) && (st.Eval(e) &&  st in post)
    case Assume(e)      => e.IsDefinedOn(st.Keys) && (st.Eval(e) ==> st in post)
    case Seq(ss)        => SeqSem(ss, st, post)
    case Assign(x, v)   => v.IsDefinedOn(st.Keys) && st.Update(x, st.Eval(v)) in post
    case VarDecl(v, s)  => forall b: Value :: Sem(s, st.Update(v, b), iset st': State | VarDeclWitness(st', v, post))
    case Choice(s0, s1) => Sem(s0, st, post) && Sem(s1, st, post)
  }

  ghost function WP(s: Stmt, post: iset<State>) : iset<State> {
    iset st: State | Sem(s, st, post)
  }

  least predicate SeqSem(ss: seq<Stmt>, st: State, post: iset<State>) {
    if ss == [] then st in post else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, post) ==> st in post') ==> Sem(ss[0], st, post')
  }

  ghost function SeqWP(ss: seq<Stmt>, post: iset<State>): iset<State> {
    iset st: State | SeqSem(ss, st, post)
  }

  lemma SemCons(s: Stmt, st: State, post: iset<State>, post': iset<State>)
    requires Sem(s, st, post)
    requires post <= post'
    ensures Sem(s, st, post')
  {
    match s
    case VarDecl(v, s) =>
      assert (iset st': State | VarDeclWitness(st', v, post)) <= (iset st': State | VarDeclWitness(st', v, post'));
    case Seq(ss) => SeqSemCons(ss, st, post, post');
    case _ =>
  }

  lemma SeqSemCons(ss: seq<Stmt>, st: State, post: iset<State>, post': iset<State>)
    requires SeqSem(ss, st, post)
    requires post <= post'
    ensures SeqSem(ss, st, post')
  {

  }

  lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, post: iset<State>) 
    requires SeqSem([s] + ss, st, post)
    ensures Sem(s, st, SeqWP(ss, post))
  {
    assert ([s] + ss)[0] == s;
  }

  lemma SemUnNest(s: Stmt, ss: seq<Stmt>, st: State, post: iset<State>) 
    requires Sem(s, st, SeqWP(ss, post))
    ensures SeqSem([s] + ss, st, post)
  {
    forall post': iset<State> | SeqWP(ss, post) <= post' {
      SemCons(s, st, SeqWP(ss, post), post');
    }
  }

  lemma SeqSemNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, post: iset<State>) 
    requires SeqSem(ss1 + ss2, st, post)
    ensures SeqSem(ss1, st, SeqWP(ss2, post))
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
    }
  }

  lemma SeqSemUnNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, post: iset<State>) 
    requires SeqSem(ss1, st, SeqWP(ss2, post))
    ensures SeqSem(ss1 + ss2, st, post)
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
    }
  }

  lemma SeqLemma(ss: seq<Stmt>, cont: seq<Stmt>, st: State, post: iset<State>)
    requires Sem(Seq(ss + cont), st, post)
    ensures SeqSem([Seq(ss)] + cont, st, post)
  {
    SeqSemNest(ss, cont, st, post);
    SemUnNest(Seq(ss), cont, st, post);
  }

  lemma SeqChoiceLemma(s0: Stmt, s1: Stmt, cont: seq<Stmt>, st: State, post: iset<State>)
    requires SeqSem([s0] + cont, st, post) 
    requires SeqSem([s1] + cont, st, post)
    ensures SeqSem([Choice(s0, s1)] + cont, st, post)
  {
    SemNest(s0, cont, st, post);
    SemNest(s1, cont, st, post);
    SemUnNest(Choice(s0, s1), cont, st, post);
  }

}