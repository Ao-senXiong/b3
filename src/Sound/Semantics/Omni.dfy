module Omni {
  import opened Defs
  export
    provides Defs
    reveals Sem, SeqSem, VarDeclWitness

  // least predicate VarDeclWitness(s: Stmt, a: State, v: Variable, post: iset<State>, post': iset<State>) {
  //   && (forall out <- post' :: out - {v} in post)
  //   && (forall b: Value :: Sem(s, a.Update(v, b), post'))
  // }

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

  least predicate SeqSem(ss: seq<Stmt>, st: State, post: iset<State>) {
    if ss == [] then st in post else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, post) ==> st in post') ==> Sem(ss[0], st, post')
  }
}