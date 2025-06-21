module Verifier {
  import opened Std.Wrappers
  import opened Basics
  import opened RawAst
  import opened Solvers
  import opened SolverExpr
  import WF = WellFormednessConsequences

  newtype Incarnations = map<Variable, Var>
  {
    method New(v: Variable) returns (x: Var) {
      x := new Var(v.name);
    }
    method NewWithSuffix(v: Variable, suffix: string) returns (x: Var) {
      x := new Var(v.name + suffix);
    }
    function Eval(e: Expr): SExpr
    { CreateTrue() } // TODO
    function DomainRestrict(s: set<Variable>): Incarnations {
      map v | v in this && v in s :: this[v]
    }
  }

  function IdExpr(v: Var): SExpr {
    CreateIdExpr(v)
  }

  // TODO: we should really start from a resolved AST
  function NameToResolvedVariable(name: string): Variable
  { Variable(name, Types.IntTypeName, VariableKind.Local) } // TODO

  // map from block names to pairs (V, Ss) of variable sets and statement sequences
  type BlockContinuations = map<Label, Continuation>
  datatype Continuation = Continuation(V: set<Variable>, continuation: seq<Stmt>)

  ghost predicate BValid(B: BlockContinuations, b3: Program) {
    forall s <- B :: WF.StmtSeq(B[s].continuation, b3)
  }

  method Process(stmts: seq<Stmt>, incarnations: Incarnations, B: BlockContinuations, o: Solver, b3: Program)
    requires WF.StmtSeq(stmts, b3) && BValid(B, b3)
    decreases StmtListMeasure(stmts) + ContinuationsMeasure(B)
  {
    if |stmts| == 0 {
      return;
    }

    var s0, cont := stmts[0], stmts[1..];
    assert StmtListMeasure(stmts) == StmtMeasure(s0) + StmtListMeasure(cont);
    match s0
    case VarDecl(v) =>
      var x := incarnations.New(v);
      Process(cont, incarnations[v := x], B, o, b3);
    case ValDecl(v, rhs) =>
      var x := incarnations.New(v);
      Process(cont, incarnations[v := x], B, o, b3);
    case Assign(lhs, rhs) =>
      var x := NameToResolvedVariable(lhs);
      var e' := incarnations.Eval(rhs);
      var x' := incarnations.New(x);
      var o' := o.Extend(CreateEq(IdExpr(x'), e'));
      Process(cont, incarnations[x := x'], B, o', b3);
    case Block(lbl, bodyStmts) =>
      var B' := B[lbl := Continuation(incarnations.Keys, cont)];
      assert StmtListMeasure(stmts) + ContinuationsMeasure(B) > StmtListMeasure(bodyStmts + [Exit(lbl)]) + ContinuationsMeasure(B') by {
        assert StmtMeasure(s0) > StmtListMeasure(bodyStmts + [Exit(lbl)]) by {
          assert StmtMeasure(s0) == 2 + StmtListMeasure(bodyStmts);
          AboutStmtListMeasureSingleton(Exit(lbl));
          AboutStmtListMeasureConcat(bodyStmts, [Exit(lbl)]);
        }
        assert ContinuationsMeasure(B) + StmtListMeasure(cont) >= ContinuationsMeasure(B') by {
          AboutContinuationsMeasureUpdate(B, lbl, incarnations.Keys, cont);
        }

        calc {
          StmtListMeasure(stmts) + ContinuationsMeasure(B);
        ==  // by assertion before `match`
          StmtMeasure(s0) + StmtListMeasure(cont) + ContinuationsMeasure(B);
        >  // by first assertion-by above
          StmtListMeasure(bodyStmts + [Exit(lbl)]) + StmtListMeasure(cont) + ContinuationsMeasure(B);
        >=  // by second assert-by above
          StmtListMeasure(bodyStmts + [Exit(lbl)]) + ContinuationsMeasure(B');
        }
      }
      WF.AboutBlockStmts(s0, b3);
      assert WF.StmtSeq(bodyStmts + [Exit(lbl)], b3);
      Process(bodyStmts + [Exit(lbl)], incarnations, B', o, b3);
    case Call(name, args) =>
      ProcessCall(name, args, cont, incarnations, B, o, b3);
    case Check(cond) =>
      var e' := incarnations.Eval(cond);
      o.Prove(e');
      Process(cont, incarnations, B, o, b3);
    case Assume(cond) =>
      var e' := incarnations.Eval(cond);
      var o' := o.Extend(e');
      Process(cont, incarnations, B, o', b3);
    case Assert(cond) =>
      var e' := incarnations.Eval(cond);
      o.Prove(e');
      var o' := o.Extend(e');
      Process(cont, incarnations, B, o', b3);
    case AForall(v, body) =>
      WF.AboutAForall(s0, b3);
      var x := incarnations.New(v);
      Process([body], incarnations[v := x], B, o, b3) by {
        assert WF.Stmt(body, b3);
        assert StmtMeasure(s0) > StmtMeasure(body);
        AboutStmtListMeasureSingleton(body);
      }

      var L := Learn(s0);
      var e' := incarnations.Eval(L);
      var o' := o.Extend(e');
      Process(cont, incarnations, B, o', b3);
    case If(cond, thn, els) =>
      WF.AboutIf(s0, b3);
      var e' := incarnations.Eval(cond);
      var oThen := o.Extend(e');
      Process([thn] + cont, incarnations, B, oThen, b3);
      var oElse := o.Extend(CreateNegation(e'));
      Process([els] + cont, incarnations, B, oElse, b3);
    case IfCase(cases) =>
      WF.AboutIfCase(s0, b3);
      for i := 0 to |cases|
        invariant CaseMeasure(s0, cases[i..]) < StmtMeasure(s0)
      {
        var cs := cases[i];
        var e' := incarnations.Eval(cs.cond);
        var o' := o.Extend(e');
        Process([cs.body] + cont, incarnations, B, o', b3);
      }
    case Loop(lbl, invariants, body) =>
      // TODO
    case Exit(lbl) =>
      expect lbl in B;
      ProcessExit(lbl, incarnations, B, o, b3);
    case Return =>
      expect ReturnLabel in B;
      ProcessExit(ReturnLabel, incarnations, B, o, b3);
    case Probe(e) =>
      var e' := incarnations.Eval(e);
      var o' := o.Record(e');
      Process(cont, incarnations, B, o', b3);
  }

  method ProcessExit(lbl: Label, incarnations: Incarnations, B: BlockContinuations, o: Solver, b3: Program)
    requires BValid(B, b3) && lbl in B
    decreases 1 + ContinuationsMeasure(B), 0
  {
      var Continuation(V, cont) := B[lbl];
      var incarnations' := incarnations.DomainRestrict(V);
      var B0 := B - {lbl};
      assert B == B0[lbl := Continuation(V, cont)];
      assert ContinuationsMeasure(B) >= StmtListMeasure(cont) + ContinuationsMeasure(B0) by {
        AboutContinuationsMeasure(B0, lbl, V, cont);
      }
      Process(cont, incarnations', B0, o, b3);
  }

  method ProcessCall(name: string, args: seq<CallArgument>, cont: seq<Stmt>, incarnations: Incarnations, B: BlockContinuations, o: Solver, b3: Program)
  {
    var maybeProc := b3.FindProcedure(name);
    if maybeProc == None {
      return;
    }
    var proc := maybeProc.value;

    var formalIns, actualIns, formalInOuts, oldInOuts, actualInOuts, formalOuts, actualOuts := CollateParameters(proc, args, b3);

    var e := SeqMap(actualIns, actualIn => incarnations.Eval(actualIn));
    /* TODO
    var x' := NewVars(formalIns, incarnations, "%in");
    var b' := NewVars(oldInOuts, incarnations);
    var b'' := NewVars(actualInOuts, incarnations);
    var c' := NewVars(actualOuts, incarnations);
    var incarnations' :=
      (map i | 0 <= i < |formalIns| :: formalIns[i] := x'[i]) +
      (map i | 0 <= i < |formalInOuts| :: formalInOuts[i] := b'[i]);

    var Pre := ConvertToChecks(proc.pre);
    var o' := o.Extend(CreateBigAnd(seq(|x'|, i requires 0 <= i < |x'| => CreateEq(x'[i], e[i]))));
    Process(Pre, incarnations', B, o');

    incarnations' :=
      (map i | 0 <= i < |formalIns| :: formalIns[i] := x'[i]) +
      (map i | 0 <= i < |formalInOuts| :: OldName(formalInOuts[i]) := b'[i]) +
      (map i | 0 <= i < |formalInOuts| :: formalInOuts[i] := b''[i]) +
      (map i | 0 <= i < |formalOuts| :: formalOuts[i] := c'[i]);
    var Post := ConvertToLearn(proc.post);
    Process(Post + cont, incarnations', B, o');
    */
  }

  method NewVars(vars: seq<Variable>, incarnations: Incarnations, suffix: string := "") returns (newVars: seq<Var>)
    ensures |newVars| == |vars|
  {
    newVars := [];
    for i := 0 to |vars|
      invariant |newVars| == i
    {
      var y := incarnations.NewWithSuffix(vars[i], suffix);
      newVars := newVars + [y];
    }
  }

  method CollateParameters(proc: Procedure, args: seq<CallArgument>, b3: Program) returns (
      formalIns: seq<Variable>, actualIns: seq<Expr>,
      formalInOuts: seq<Variable>, oldInOuts: seq<Variable>, actualInOuts: seq<Variable>,
      formalOuts: seq<Variable>, actualOuts: seq<Variable>)
    ensures |formalIns| == |actualIns|
    ensures |formalInOuts| == |oldInOuts| == |actualInOuts|
    ensures |formalOuts| == |actualOuts|
    ensures Variable.UniqueNames(formalIns)
    ensures Variable.UniqueNames(formalInOuts)
  {
    formalIns, actualIns := [], [];
    formalInOuts, oldInOuts, actualInOuts := [], [], [];
    formalOuts, actualOuts := [], [];
    /* TODO
    for i := 0 to |proc.parameters|
    {
      match proc.parameters[i].kind
    }
    */
  }

  ghost function StmtListMeasure(stmts: seq<Stmt>): nat {
    if stmts == [] then 0 else StmtMeasure(stmts[0]) + StmtListMeasure(stmts[1..])
  }
  ghost function StmtMeasure(stmt: Stmt): nat
    ensures 0 < StmtMeasure(stmt)
  {
    match stmt
    case VarDecl(_) => 1
    case ValDecl(_, _) => 1
    case Assign(_, _) => 1
    case Block(_, stmts) => 2 + StmtListMeasure(stmts)
    case Call(name, args) => 1 // TODO
    case Check(cond) => 1
    case Assume(cond) => 1
    case Assert(cond) => 2
    case AForall(v, body) => 1 + StmtMeasure(body)
    case If(cond, thn, els) => 1 + StmtMeasure(thn) + StmtMeasure(els)
    case IfCase(cases) => 1 + CaseMeasure(stmt, cases)
    case Loop(lbl, invariants, body) => 1 + StmtMeasure(body) // TODO
    case Exit(lbl) => 1
    case Return => 1
    case Probe(e) => 1
  }
  ghost function CaseMeasure(stmt: Stmt, cases: seq<Case>): nat
    requires forall cs <- cases :: cs < stmt
  {
    if cases == [] then 0 else
      assert cases[0] in cases && forall cs <- cases[1..] :: cs in cases;
      StmtMeasure(cases[0].body) + CaseMeasure(stmt, cases[1..])
  }

  lemma AboutStmtListMeasureSingleton(s: Stmt)
    ensures StmtListMeasure([s]) == StmtMeasure(s)
  {}

  lemma AboutStmtListMeasureConcat(a: seq<Stmt>, b: seq<Stmt>)
    ensures StmtListMeasure(a + b) == StmtListMeasure(a) + StmtListMeasure(b)
  {
    if a == [] {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
    }
  }

  ghost function ContinuationsMeasure(B: BlockContinuations): nat {
    if |B| == 0 then 0 else
      var lbl := Pick(B.Keys);
      StmtListMeasure(B[lbl].continuation) + ContinuationsMeasure(B - {lbl})
  }
  ghost function Pick<X>(s: set<X>): X
    requires |s| != 0
  {
    var x :| x in s; x
  }
  lemma AboutContinuationsMeasure(B: BlockContinuations, x: Label, V: set<Variable>, cont: seq<Stmt>)
    requires x !in B
    ensures ContinuationsMeasure(B[x := Continuation(V, cont)]) == StmtListMeasure(cont) + ContinuationsMeasure(B)
  {
    var B' := B[x := Continuation(V, cont)];
    assert B'[x].continuation == cont;
    assert B' - {x} == B;
    var y := Pick(B'.Keys);
    if y == x {
      assert ContinuationsMeasure(B') == StmtListMeasure(B'[x].continuation) + ContinuationsMeasure(B);
    } else {
      var Bxy, Bx, By, B0 := B', B' - {y}, B' - {x}, B' - {x, y};
      assert By == B;
      assert Bx - {x} == B0 == By - {y};
      assert Bx == B0[x := Continuation(V, cont)];
      assert By == B0[y := B'[y]];

      var V', cont' := B'[y].V, B'[y].continuation;
      calc {
        ContinuationsMeasure(Bxy);
      ==
        StmtListMeasure(cont') + ContinuationsMeasure(Bx);
      ==  { AboutContinuationsMeasure(B0, x, V, cont); }
        StmtListMeasure(cont') + StmtListMeasure(cont) + ContinuationsMeasure(B0);
      ==
        StmtListMeasure(cont) + StmtListMeasure(cont') + ContinuationsMeasure(B0);
      ==  { AboutContinuationsMeasure(B0, y, V', cont'); }
        StmtListMeasure(cont) + ContinuationsMeasure(By);
      }
    }
  }

  lemma AboutContinuationsMeasureRemove(B: BlockContinuations, lbl: Label)
    ensures ContinuationsMeasure(B) >= ContinuationsMeasure(B - {lbl})
  {
    if lbl in B {
      var B0 := B - {lbl};
      var V, cont := B[lbl].V, B[lbl].continuation;
      assert B == B0[lbl := Continuation(V, cont)];
      AboutContinuationsMeasure(B0, lbl, B[lbl].V, B[lbl].continuation);
      assert ContinuationsMeasure(B0[lbl := Continuation(V, cont)]) == StmtListMeasure(cont) + ContinuationsMeasure(B0);
    } else {
      assert B == B - {lbl};
    }
  }

  lemma AboutContinuationsMeasureUpdate(B: BlockContinuations, lbl: Label, V: set<Variable>, cont: seq<Stmt>)
    ensures ContinuationsMeasure(B) + StmtListMeasure(cont) >= ContinuationsMeasure(B[lbl := Continuation(V, cont)])
  {
    var B' := B[lbl := Continuation(V, cont)];
    if lbl in B {
      var B0 := B - {lbl};
      calc {
        ContinuationsMeasure(B) + StmtListMeasure(cont);
      >=  { AboutContinuationsMeasureRemove(B, lbl); }
        ContinuationsMeasure(B0) + StmtListMeasure(cont);
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