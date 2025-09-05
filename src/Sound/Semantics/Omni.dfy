module Omni {
  import opened Defs
  export
    provides Defs, SeqLemma, SemNest, WP, SemCons, SeqFrameLemmaAll
    reveals Sem, SeqSem, SeqWP, Continuation, Continuation.LessThan, Continuation.Update, Continuation.Delete

  newtype Continuation = map<Label, iset<State>> {
    predicate LessThan(cont: Continuation) {
      && Keys <= cont.Keys
      && forall lbl <- Keys :: this[lbl] <= cont[lbl]
    }

    ghost function Update(v: Variable) : Continuation {
      map lbl | lbl in Keys :: UpdateSet(v, this[lbl])
    }

    ghost function Delete(v: Variable) : Continuation {
      map lbl | lbl in Keys :: DeleteSet(v, this[lbl])
    }
  }

  /**
    (l :: var y; exit l); y := 0
    wp ((l :: var y; exit l); y := 0, True, {}) == 
    wp ((l ::var y; exit l), wp(y := 0, True, {}), {}) == 
    wp ((l ::var y; exit l), fun st => y in st, {}) == 
    wp ((var y; exit l), fun st => y in st, {l |-> fun st => y in st}) == 
    fun st => forall b: bool, wp ((exit l), False, {l |-> fun st => y in st}) st[y := b]
    fun st => forall b: bool, y in st[y := b]
   */

  least predicate Sem(s: Stmt, st: State, post: iset<State>, cont: Continuation) {
    match s
    case Check(e)            => e.IsDefinedOn(st.Keys) && (st.Eval(e) &&  st in post)
    case Assume(e)           => e.IsDefinedOn(st.Keys) && (st.Eval(e) ==> st in post)
    case Seq(ss)             => SeqSem(ss, st, post, cont)
    case Assign(x, v)        => 
      && x in st
      && v.IsDefinedOn(st.Keys) 
      && st.Update(x, st.Eval(v)) in post
    case VarDecl(v, s)       => forall b: Value :: Sem(s, st.Update(v, b), UpdateSet(v, post), cont.Update(v))
    case Choice(s0, s1)      => Sem(s0, st, post, cont) && Sem(s1, st, post, cont)
    case LabeledStmt(lbl, s) => Sem(s, st, post, cont[lbl := post])
    case Exit(lbl)           => lbl in cont && st in cont[lbl]
  }

  ghost function WP(s: Stmt, post: iset<State>, cont: Continuation) : iset<State> {
    iset st: State | Sem(s, st, post, cont)
  }

  least predicate SeqSem(ss: seq<Stmt>, st: State, post: iset<State>, cont: Continuation) {
    if ss == [] then st in post else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, post, cont) ==> st in post') ==> Sem(ss[0], st, post', cont)
  }

  ghost function SeqWP(ss: seq<Stmt>, post: iset<State>, cont: Continuation): iset<State> {
    iset st: State | SeqSem(ss, st, post, cont)
  }

  lemma SemConsCont(s: Stmt, st: State, post: iset<State>, post': iset<State>, cont: Continuation, cont': Continuation)
    requires Sem(s, st, post, cont)
    requires post <= post'
    requires cont.LessThan(cont')
    ensures Sem(s, st, post', cont')
  {
    match s
    case VarDecl(v, s) => 
      assert cont.Update(v).LessThan(cont'.Update(v));
      assert UpdateSet(v, post) <= UpdateSet(v, post');
    case Seq(ss) => SeqSemConsCont(ss, st, post, post', cont, cont');
    case LabeledStmt(lbl, s) => assert cont[lbl := post].LessThan(cont'[lbl := post']);
    case _ =>
  }

  lemma SeqSemConsCont(ss: seq<Stmt>, st: State, post: iset<State>, post': iset<State>, cont: Continuation, cont': Continuation)
    requires SeqSem(ss, st, post, cont)
    requires post <= post'
    requires cont.LessThan(cont')
    ensures SeqSem(ss, st, post', cont')
  {
    if ss != [] {
      forall post'': iset<State> | SeqWP(ss[1..], post', cont') <= post''
        ensures Sem(ss[0], st, post'', cont') {
        SemConsCont(ss[0], st, post'', post'', cont, cont');
      }
    }
  }

  least lemma SemCons(s: Stmt, st: State, post: iset<State>, post': iset<State>, cont: Continuation)
    requires Sem(s, st, post, cont)
    requires post <= post'
    ensures Sem(s, st, post', cont)
  { SemConsCont(s, st, post, post', cont, cont); }

  lemma SeqSemCons(ss: seq<Stmt>, st: State, post: iset<State>, post': iset<State>, cont: Continuation)
    requires SeqSem(ss, st, post, cont)
    requires post <= post'
    ensures SeqSem(ss, st, post', cont)
  { SeqSemConsCont(ss, st, post, post', cont, cont); }

  least lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, post: iset<State>, cont: Continuation) 
    requires Sem(s, st, SeqWP(ss, post, cont), cont)
    ensures SeqSem([s] + ss, st, post, cont)
  {
    forall post': iset<State> | SeqWP(ss, post, cont) <= post' {
      SemCons(s, st, SeqWP(ss, post, cont), post', cont);
    }
  }

  lemma SeqSemNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, post: iset<State>, cont: Continuation) 
    requires SeqSem(ss1 + ss2, st, post, cont)
    ensures SeqSem(ss1, st, SeqWP(ss2, post, cont), cont)
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
    }
  }

  lemma SeqLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, post: iset<State>, cont: Continuation)
    requires Sem(Seq(ss1 + ss2), st, post, cont)
    ensures SeqSem([Seq(ss1)] + ss2, st, post, cont)
  {
    SeqSemNest(ss1, ss2, st, post, cont);
    SemNest(Seq(ss1), ss2, st, post, cont);
  }

  lemma FrameLemma(s: Stmt, v: Variable, st: State, post: iset<State>, cont: Continuation)
    requires Sem(s, st, post, cont)
    requires v !in s.FVars()
    requires v !in s.BVars()
    ensures Sem(s, st - {v}, DeleteSet(v, post), cont.Delete(v))
  {
    match s 
    case Assign(x, e) => e.EvalFVarsLemma(st, st - {v});
    case Check(e) => e.EvalFVarsLemma(st, st - {v});
    case Assume(e) =>  e.EvalFVarsLemma(st, st - {v});
    case Seq(ss) => SeqFrameLemma(ss, v, st, post, cont);
    case VarDecl(u, s) =>
      forall c: Value {: trigger}
        ensures Sem(s, (st - {v}).Update(u, c), UpdateSet(u, DeleteSet(v, post)), cont.Delete(v).Update(u)) { 
        FrameLemma(s, v, st.Update(u, c), UpdateSet(u, post), cont.Update(u));
        assert forall c :: (st - {v}).Update(u, c) == st.Update(u, c) - {v};        
        SemConsCont(s, (st - {v}).Update(u, c), 
          DeleteSet(v, UpdateSet(u, post)), 
          UpdateSet(u, DeleteSet(v, post)), 
          cont.Update(u).Delete(v),
          cont.Delete(v).Update(u)) by {
          // forall st | st in DeleteSet(v, UpdateSet(u, post)) 
          //   ensures st in UpdateSet(u, DeleteSet(v, post)) {
          //   assert forall b :: (st - {u}).Update(v, b) == st.Update(v, b) - {u};
          // }
        }
      }
    case Choice(s0, s1) => FrameLemma(s0, v, st, post, cont); FrameLemma(s1, v, st, post, cont);
    case _ => assume {:axiom} false;
  }

  lemma SeqFrameLemma(ss: seq<Stmt>, v: Variable, st: State, post: iset<State>, cont: Continuation)
    requires SeqSem(ss, st, post, cont)
    requires v !in SeqBVars(ss)
    requires v !in SeqFVars(ss)
    ensures SeqSem(ss, st - {v}, DeleteSet(v, post), cont.Delete(v))
  {
    if ss == [] {
    } else {
      assert ([ss[0]] + ss[1..])[0] == ss[0];
      FrameLemma(ss[0], v, st, SeqWP(ss[1..], post, cont), cont);
      SemNest(ss[0], ss[1..], st - {v}, DeleteSet(v, post), cont.Delete(v)) by {
        SemCons(ss[0], st - {v}, DeleteSet(v, SeqWP(ss[1..], post, cont)), SeqWP(ss[1..], DeleteSet(v, post), cont.Delete(v)), cont.Delete(v)) by {
          forall st | st in DeleteSet(v, SeqWP(ss[1..], post, cont)) 
            ensures SeqSem(ss[1..], st, DeleteSet(v, post), cont.Delete(v)) {
            var st': State :| st == st' - {v} && SeqSem(ss[1..], st', post, cont);
            SeqFrameLemma(ss[1..], v, st', post, cont);
          }
        }
      }
    }
  }

  lemma SeqFrameLemmaAll(ss: seq<Stmt>, v: Variable, st: State, cont: Continuation)
    requires SeqSem(ss, st, AllStates, cont)
    requires v !in SeqBVars(ss)
    requires v !in SeqFVars(ss)
    ensures SeqSem(ss, st - {v}, AllStates, cont.Delete(v))
  {
    SeqFrameLemma(ss, v, st, AllStates, cont);
    SeqSemCons(ss, st - {v}, DeleteSet(v, AllStates), AllStates, cont.Delete(v));
  }
}