module BlockContinuations {
  import Ast

  export
    reveals T, Continuation
    provides Empty
    reveals Valid
    reveals StmtMeasure
    provides StmtSeqMeasure
    provides AboutStmtSeqMeasureSingleton, StmtPairMeasure, StmtMeasurePrepend, StmtMeasureSplit, AboutStmtSeqMeasureConcat, StmtSeqElement
    provides ContinuationsMeasure, AboutContinuationsMeasure, AboutContinuationsMeasureUpdate
    provides Ast

  datatype Continuation = Continuation(variablesInScope: set<Ast.Variable>, continuation: seq<Ast.Stmt>)

  type T = map<Ast.Label, Continuation>

  predicate Valid(t: T) {
    forall lbl <- t, stmt <- t[lbl].continuation :: stmt.WellFormed()
  }

  function Empty(): T
    ensures Valid(Empty())
  {
    map[]
  }

  ghost function StmtMeasure(stmt: Ast.Stmt): nat
    ensures 0 < StmtMeasure(stmt)
  {
    match stmt
    case VarDecl(_, _, body) => 1 + StmtMeasure(body)
    case Assign(_, _) => 1
    case Block(stmts) => 1 + StmtSeqMeasure(stmts)
    case Call(_, _) => 1 // TODO
    case Check(_) => 1
    case Assume(_) => 1
    case Assert(_) => 2
    case AForall(_, body) => 1 + StmtMeasure(body)
    case Choose(branches) => 1 + StmtSeqMeasure(branches)
    case Loop(_, body) => 1 + StmtMeasure(body) // TODO
    case LabeledStmt(_, body) => 2 + StmtMeasure(body)
    case Exit(_) => 1
    case Probe(_) => 1
  }

  ghost function StmtSeqMeasure(stmts: seq<Ast.Stmt>): nat {
    if stmts == [] then 0 else StmtMeasure(stmts[0]) + StmtSeqMeasure(stmts[1..])
  }

  lemma StmtSeqElement(stmts: seq<Ast.Stmt>, i: nat)
    requires i < |stmts|
    ensures StmtMeasure(stmts[i]) <= StmtSeqMeasure(stmts)
  {
    if i != 0 {
      calc {
        StmtMeasure(stmts[i]);
        { assert stmts[i] == stmts[1..][i - 1]; }
        StmtMeasure(stmts[1..][i - 1]);
      <=  { StmtSeqElement(stmts[1..], i - 1); }
        StmtSeqMeasure(stmts[1..]);
      <=
        StmtSeqMeasure(stmts);
      }
      
    }
  }

  lemma AboutStmtSeqMeasureSingleton(s: Ast.Stmt)
    ensures StmtSeqMeasure([s]) == StmtMeasure(s)
  {}

  lemma StmtPairMeasure(a: Ast.Stmt, b: Ast.Stmt)
    ensures StmtSeqMeasure([a, b]) == StmtMeasure(a) + StmtMeasure(b)
  {
    calc {
      StmtSeqMeasure([a, b]);
      { assert [a, b][1..] == [b]; }
      StmtMeasure(a) + StmtSeqMeasure([b]);
      { AboutStmtSeqMeasureSingleton(b); }
      StmtMeasure(a) + StmtMeasure(b);
    }
  }

  lemma AboutStmtSeqMeasureConcat(a: seq<Ast.Stmt>, b: seq<Ast.Stmt>)
    ensures StmtSeqMeasure(a + b) == StmtSeqMeasure(a) + StmtSeqMeasure(b)
  {
    if a == [] {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
    }
  }

  lemma StmtMeasurePrepend(stmt: Ast.Stmt, stmts: seq<Ast.Stmt>)
    ensures StmtSeqMeasure([stmt] + stmts) == StmtMeasure(stmt) + StmtSeqMeasure(stmts)
  {
    AboutStmtSeqMeasureSingleton(stmt);
    AboutStmtSeqMeasureConcat([stmt], stmts);
  }

  lemma StmtMeasureSplit(stmts: seq<Ast.Stmt>)
    requires stmts != []
    ensures StmtSeqMeasure(stmts) == StmtMeasure(stmts[0]) + StmtSeqMeasure(stmts[1..])
  {
    assert [stmts[0]] + stmts[1..] == stmts;
    StmtMeasurePrepend(stmts[0], stmts[1..]);
  }

  ghost function ContinuationsMeasure(B: T): nat {
    if |B| == 0 then 0 else
      var lbl := Pick(B.Keys);
      StmtSeqMeasure(B[lbl].continuation) + ContinuationsMeasure(B - {lbl})
  }

  ghost function Pick<X>(s: set<X>): X
    requires |s| != 0
  {
    var x :| x in s; x
  }

  lemma AboutContinuationsMeasure(B: T, x: Ast.Label, V: set<Ast.Variable>, cont: seq<Ast.Stmt>)
    requires x !in B
    ensures ContinuationsMeasure(B[x := Continuation(V, cont)]) == ContinuationsMeasure(B) + StmtSeqMeasure(cont)
  {
    var B' := B[x := Continuation(V, cont)];
    assert B'[x].continuation == cont;
    assert B' - {x} == B;
    var y := Pick(B'.Keys);
    if y == x {
      assert ContinuationsMeasure(B') == StmtSeqMeasure(B'[x].continuation) + ContinuationsMeasure(B);
    } else {
      var Bxy, Bx, By, B0 := B', B' - {y}, B' - {x}, B' - {x, y};
      assert By == B;
      assert Bx - {x} == B0 == By - {y};
      assert Bx == B0[x := Continuation(V, cont)];
      assert By == B0[y := B'[y]];

      var V', cont' := B'[y].variablesInScope, B'[y].continuation;
      calc {
        ContinuationsMeasure(Bxy);
      ==
        StmtSeqMeasure(cont') + ContinuationsMeasure(Bx);
      ==  { AboutContinuationsMeasure(B0, x, V, cont); }
        StmtSeqMeasure(cont') + StmtSeqMeasure(cont) + ContinuationsMeasure(B0);
      ==
        StmtSeqMeasure(cont) + StmtSeqMeasure(cont') + ContinuationsMeasure(B0);
      ==  { AboutContinuationsMeasure(B0, y, V', cont'); }
        StmtSeqMeasure(cont) + ContinuationsMeasure(By);
      }
    }
  }

  lemma AboutContinuationsMeasureRemove(B: T, lbl: Ast.Label)
    ensures ContinuationsMeasure(B) >= ContinuationsMeasure(B - {lbl})
  {
    if lbl in B {
      var B0 := B - {lbl};
      var V, cont := B[lbl].variablesInScope, B[lbl].continuation;
      assert B == B0[lbl := Continuation(V, cont)];
      AboutContinuationsMeasure(B0, lbl, B[lbl].variablesInScope, B[lbl].continuation);
      assert ContinuationsMeasure(B0[lbl := Continuation(V, cont)]) == StmtSeqMeasure(cont) + ContinuationsMeasure(B0);
    } else {
      assert B == B - {lbl};
    }
  }

  lemma AboutContinuationsMeasureUpdate(B: T, lbl: Ast.Label, V: set<Ast.Variable>, cont: seq<Ast.Stmt>)
    ensures ContinuationsMeasure(B) + StmtSeqMeasure(cont) >= ContinuationsMeasure(B[lbl := Continuation(V, cont)])
  {
    var B' := B[lbl := Continuation(V, cont)];
    if lbl in B {
      var B0 := B - {lbl};
      calc {
        ContinuationsMeasure(B) + StmtSeqMeasure(cont);
      >=  { AboutContinuationsMeasureRemove(B, lbl); }
        ContinuationsMeasure(B0) + StmtSeqMeasure(cont);
      >=  { AboutContinuationsMeasure(B0, lbl, V, cont); }
        ContinuationsMeasure(B0[lbl := Continuation(V, cont)]);
      ==  { assert B' == B0[lbl := Continuation(V, cont)] == B'; }
        ContinuationsMeasure(B');
      }
    } else {
      AboutContinuationsMeasure(B, lbl, V, cont);
    }
  }
}