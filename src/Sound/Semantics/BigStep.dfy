module BigStep {
  import opened Defs

  export 
    reveals Sem, SeqSem
    provides Defs
    provides SeqChoiceLemma, SeqFrameLemma, SeqLemma

  least predicate Sem[nat](s: Stmt, a: State, z: Except<State>) 
  {
    match s
    case Check(e) =>
      e.IsDefinedOn(a.Keys) &&
      z == if a.Eval(e) then Ok(a) else Error
    case Assume(e) =>
      e.IsDefinedOn(a.Keys) &&
      a.Eval(e) && z == Ok(a)
    case Seq(ss) => SeqSem(ss, a, z)
    case Assign(x, v) =>
      && v.IsDefinedOn(a.Keys) 
      && z == Ok(a.Update(x, a.Eval(v)))
    case VarDecl(v, s) => exists b :: 
      && Sem(s, a.Update(v, b), ExceptUpdate(z, v, b))
      && (z.Ok? ==> v !in z.Extract().Keys)
    case Choice(s0, s1) => Sem(s0, a, z) || Sem(s1, a, z)
    // case While(guard, inv, body) =>
    //   if a.Eval(guard) then
    //     Sem(Seq(body, While(guard, inv, body)), a, z)
    // else z == Ok(a)
  }

  least predicate SeqSem[nat](ss: seq<Stmt>, a: State, z: Except<State>) 
  {
    if ss == [] then z == Ok(a) else
      exists w ::
        && Sem(ss[0], a, w)
        && match w {
            case Ok(b) => SeqSem(ss[1..], b, z)
            case _ => z == w
        }
  }

  lemma SeqConcatOkLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, st': State, out: Except<State>)
    requires SeqSem(ss1, st, Ok(st'))
    requires SeqSem(ss2, st', out)
    ensures SeqSem(ss1 + ss2, st, out)
  { 
    if ss1 != [] {
      var w :| Sem(ss1[0], st, Ok(w)) && SeqSem(ss1[1..], w, Ok(st'));
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
    } else {
      assert [] + ss2 == ss2;
    }
  }

  lemma SeqConcatErrorLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State)
    requires SeqSem(ss1, st, Error)
    ensures SeqSem(ss1 + ss2, st, Error)
  { 
    if ss1 != [] {
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2);
      var w :| Sem(ss1[0], st, w) && match w {
            case Ok(b) => SeqSem(ss1[1..], b, Error)
            case _ => Error == w };
      match w
      case Ok(st') => assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      case _ => assert (ss1 + ss2)[0] == ss1[0];
    }
  }

  lemma SeqLemma(ss: seq<Stmt>, cont: seq<Stmt>, st: State, out: Except<State>)
    requires SeqSem([Seq(ss)] + cont, st, out)
    ensures Sem(Seq(ss + cont), st, out)
  {
    assert SeqSem(ss + cont, st, out) by {
    // if st' :| Sem(Seq(ss), st, Ok(st')) && SeqSem(cont, st', out) {
    //   SeqBigStepConcatOkLemma(ss, cont, st, st', out);
    // } else {
    //   SeqBigStepConcatErrorLemma(ss, cont, st);
    // }
    if 
    case st' :| Sem(Seq(ss), st, Ok(st')) && SeqSem(cont, st', out) => 
      SeqConcatOkLemma(ss, cont, st, st', out);
    case Sem(Seq(ss), st, out) && out.IsFailure() => 
      SeqConcatErrorLemma(ss, cont, st);
    }
    //   /* 
    //   if st' :| Sem(Seq(ss), st, ()) && 
    //   */
    //   var w :| Sem(Seq(ss), st, w) && 
    //     match w {
    //         case Ok(b) => SeqSem(cont, b, out)
    //         case _ => out == w
    //     };
    //   match w
    //   case Ok(st') =>
    //     SeqBigStepConcatOkLemma(ss, cont, st, st', out);
    //   case _ =>
    //     SeqBigStepConcatErrorLemma(ss, cont, st);
    // }
  } 

  lemma SeqChoiceLemma(s0: Stmt, s1: Stmt, cont: seq<Stmt>, st: State, out: Except<State>)
    requires SeqSem([Choice(s0, s1)] + cont, st, out)
    ensures SeqSem([s0] + cont, st, out) || SeqSem([s1] + cont, st, out)
  {
    assert forall s :: ([s] + cont)[0] == s;
    var w :| Sem(Choice(s0, s1), st, w) && match w {
      case Ok(b) => SeqSem(cont, b, out)
      case _ => out == w
    };
    if Sem(s0, st, w) {
      assert SeqSem([s0] + cont, st, out);
    } else {
      assert Sem(s1, st, w);
      assert SeqSem([s1] + cont, st, out);
    }
  }

  lemma FrameLemma(s: Stmt, v: Variable, b: Value, st: State, out: Except<State>)
    requires Sem(s, st, out)
    requires v !in s.FVars()
    requires v !in s.BVars()
    ensures Sem(s, st.Update(v, b), ExceptUpdate(out, v, b))
  {
    match s
    case Assign(x, e) => 
      e.EvalFVarsLemma(st, st.Update(v, b));
      var ev := st.Eval(e);
      assert st.Update(v, b).Update(x, ev) == st.Update(x, ev).Update(v, b);
    case Check(e) => e.EvalFVarsLemma(st, st.Update(v, b));
    case Assume(e) => e.EvalFVarsLemma(st, st.Update(v, b));
    case Seq(ss) => SeqFrameLemma(ss, v, b, st, out);
    case VarDecl(u, s) =>
      var c :| 
        && Sem(s, st.Update(u, c), ExceptUpdate(out, u, c))
        && (out.Ok? ==> u !in out.Extract().Keys);
      FrameLemma(s, v, b, st.Update(u, c), ExceptUpdate(out, u, c));
      assert st.Update(v, b).Update(u, c) == st.Update(u, c).Update(v, b);
      assert ExceptUpdate(ExceptUpdate(out, u, c), v, b) == ExceptUpdate(ExceptUpdate(out, v, b), u, c) by {
        match out
        case Ok(st') =>
          assert st'.Update(v, b).Update(u, c) == st'.Update(u, c).Update(v, b);
        case _ =>
      }
    case Choice(s0, s1) =>
  }

  lemma SeqFrameLemma(ss: seq<Stmt>, v: Variable, b: Value, st: State, out: Except<State>)
    requires SeqSem(ss, st, out)
    requires v !in SeqFVars(ss)
    requires v !in SeqBVars(ss)
    ensures SeqSem(ss, st.Update(v, b), ExceptUpdate(out, v, b))
  {
    if ss == [] {
    } else {
      var w :| Sem(ss[0], st, w) && match w {
        case Ok(st') => SeqSem(ss[1..], st', out)
        case _ => out == w
      };
      FrameLemma(ss[0], v, b, st, w);
    }
  }
}