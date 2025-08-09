module Verifier {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import opened SolverExpr
  import RSolvers

  export
    provides Verify
    provides Ast

  method Verify(b3: Ast.Program)
    requires b3.WellFormed()
  {
    var procs := b3.procedures;
    while procs != {}
    {
      var proc: Procedure :| proc in procs;
      procs := procs - {proc};

      print "Verifying ", proc.Name, " ...\n";
      VerifyProcedure(proc);
    }
  }

  method VerifyProcedure(proc: Ast.Procedure)
    requires proc.WellFormed()
  {
    var smtEngine := RSolvers.CreateEngine();
    var context := RSolvers.CreateEmptyContext();

    // Create incarnations for parameters in the pre-state
    var preIncarnations, bodyIncarnations := CreateProcIncarnations(proc.Parameters);

    // Assume precondition (TODO: should also vet precondition)
    for i := 0 to |proc.Pre|
      invariant smtEngine.Valid()
    {
      match proc.Pre[i]
      case AExpr(e) =>
        context := RSolvers.Extend(context, preIncarnations.REval(e));
      case _ => // TODO
    }

    if proc.Body.Some? {
      var cp;
      bodyIncarnations, context, cp := ProcessStmt(proc.Body.value, bodyIncarnations, context, smtEngine);
      expect cp == Normal; // TODO: this holds if all exit in the body go to defined labels
    }

    // Check postcondition (TODO: should also vet postcondition)
    for i := 0 to |proc.Post|
      invariant smtEngine.Valid()
    {
      match proc.Post[i]
      case AExpr(e) =>
        smtEngine.Prove(context, bodyIncarnations.REval(e));
      case _ => // TODO
    }
  }

  method CreateProcIncarnations(parameters: seq<Parameter>) returns (preIncarnations: Incarnations, bodyIncarnations: Incarnations)
    requires forall i :: 0 <= i < |parameters| ==> parameters[i].WellFormed()
  {
    preIncarnations, bodyIncarnations := map[], map[];
    for i := 0 to |parameters| {
      var parameter := parameters[i];
      match parameter.mode
      case In =>
        var v := new SVar(parameter.name);
        preIncarnations := preIncarnations[parameter := v];
        bodyIncarnations := bodyIncarnations[parameter := v];
      case InOut =>
        var vOld := new SVar(parameter.name + "%old");
        preIncarnations := preIncarnations[parameter := vOld];
        bodyIncarnations := bodyIncarnations[parameter.oldInOut.value := vOld];
        bodyIncarnations := bodyIncarnations[parameter := vOld];
      case out =>
        var v := new SVar(parameter.name);
        bodyIncarnations := bodyIncarnations[parameter := v];
    }
  }

  type RExpr = RSolvers.RExpr

  newtype Incarnations = map<Variable, SVar>
  {
    method Update(v: Variable) returns (incarnations: Incarnations, x: SVar) {
      var sequenceNumber := Int2String(|this|);
      x := new SVar(v.name + "%" + sequenceNumber);
      incarnations := this[v := x];
    }

    function REval(expr: Expr): RSolvers.RExpr {
      match expr
      case BConst(value) => RExpr.Boolean(value)
      case IConst(value) => RExpr.Integer(value)
      case IdExpr(v) =>
        assume {:axiom} v in this; // TODO
        RExpr.Id(this[v])
      case BinaryExpr(op, e0, e1) =>
        var s0, s1 := REval(e0), REval(e1);
        match op {
          case Eq => RExpr.Eq(s0, s1)
        }
    }

    function Eval(expr: Expr): SExpr {
      match expr
      case BConst(value) => SExpr.Boolean(value)
      case IConst(value) => SExpr.Integer(value)
      case IdExpr(v) =>
        assume {:axiom} v in this; // TODO
        SExpr.Id(this[v])
      case BinaryExpr(op, e0, e1) =>
        var s0, s1 := Eval(e0), Eval(e1);
        match op {
          case Eq => SExpr.Eq(s0, s1)
        }
    }

    function DomainRestrict(s: set<Variable>): Incarnations {
      map v | v in this && v in s :: this[v]
    }
  }

  datatype ContinuationPoint =
    | Normal
    | Abrupt(lbl: Label)

  method ProcessStmt(stmt: Stmt, incarnations_in: Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine)
      returns (incarnations: Incarnations, context: RSolvers.RContext, cp: ContinuationPoint)
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    incarnations, context, cp := incarnations_in, context_in, Normal;
    match stmt
    case VarDecl(v, init, body) =>
      var sv;
      incarnations, sv := incarnations.Update(v);
      if init.Some? {
        var sRhs := incarnations.REval(init.value);
        context := RSolvers.Extend(context, RExpr.Eq(RExpr.Id(sv), sRhs));
      }
      incarnations, context, cp := ProcessStmt(body, incarnations, context, smtEngine);
    case Assign(lhs, rhs) =>
      var sRhs := incarnations.REval(rhs);
      var sLhs;
      incarnations, sLhs := incarnations.Update(lhs);
      context := RSolvers.Extend(context, RExpr.Eq(RExpr.Id(sLhs), sRhs));
    case Block(stmts) =>
      for i := 0 to |stmts|
        invariant smtEngine.Valid()
      {
        incarnations, context, cp := ProcessStmt(stmts[i], incarnations, context, smtEngine);
        if cp.Abrupt? {
          return;
        }
      }
    case Call(_, _) =>
      print "UNHANDLED STATEMENT: Call\n"; // TODO
    case Check(cond) =>
      smtEngine.Prove(context, incarnations.REval(cond));
    case Assume(cond) =>
      context := RSolvers.Extend(context, incarnations.REval(cond));
    case Assert(cond) =>
      var e := incarnations.REval(cond);
      smtEngine.Prove(context, e);
      context := RSolvers.Extend(context, e);
    case AForall(_, _) =>
      print "UNHANDLED STATEMENT: AForall\n"; // TODO
    case Choice(_) =>
      print "UNHANDLED STATEMENT: Choice\n"; // TODO
    case Loop(_, _) =>
      print "UNHANDLED STATEMENT: Loop\n"; // TODO
    case LabeledStmt(lbl, body) =>
      incarnations, context, cp := ProcessStmt(body, incarnations, context, smtEngine);
      if cp == Abrupt(lbl) {
        cp := Normal;
      }
    case Exit(lbl) =>
      cp := Abrupt(lbl);
    case Probe(e) =>
      context := RSolvers.Record(context, incarnations.REval(e));
  }

/*
  method ProcessStmt(stmt: Stmt, incarnations: Incarnations, B: BlockContinuations, o: Solver)
    returns (incarnations': Incarnations, o': Solver)
  {
    match stmt
    case VarDecl(v, init, body) =>
      var x := incarnations.New(v);
      Process(cont, incarnations[v := x], B, o, b3);
    case Assign(x, rhs) =>
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
  }
*/

/*************************
  method Process(stmts: seq<Stmt>, incarnations: Incarnations, B: BlockContinuations, o: Solver, b3: Program)
    requires BValid(B, b3)
    decreases StmtListMeasure(stmts) + ContinuationsMeasure(B)
  {
    if |stmts| == 0 {
      return;
    }

    var s0, cont := stmts[0], stmts[1..];
    assert StmtListMeasure(stmts) == StmtMeasure(s0) + StmtListMeasure(cont);
    match s0
    case VarDecl(v, init, body) =>
      var x := incarnations.New(v);
      Process(cont, incarnations[v := x], B, o, b3);
    case Assign(x, rhs) =>
      var e' := incarnations.Eval(rhs);
      var x' := incarnations.New(x);
      var o' := o.Extend(SExpr.Eq(IdExpr(x'), e'));
      Process(cont, incarnations[x := x'], B, o', b3);
    case Block(bodyStmts) =>
      Process(bodyStmts + cont, incarnations, B, o, b3);
    case Call(proc, args) =>
      ProcessCall(proc, args, cont, incarnations, B, o, b3);
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
    case If(cases) =>
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
    case LabeledStmt(lbl, body) =>
      var B' := B[lbl := Continuation(incarnations.Keys, cont)];
      assert StmtListMeasure(stmts) + ContinuationsMeasure(B) > StmtListMeasure([body, Exit(lbl)]) + ContinuationsMeasure(B') by {
        assert StmtMeasure(s0) > StmtListMeasure([body, Exit(lbl)]) by {
          assert StmtMeasure(s0) == 2 + StmtMeasure(body);
          AboutStmtListMeasureSingleton(Exit(lbl));
          AboutStmtListMeasureConcat([body], [Exit(lbl)]); // TODO: this can probably use a more specific lemma
        }
        assert ContinuationsMeasure(B) + StmtListMeasure(cont) >= ContinuationsMeasure(B') by {
          AboutContinuationsMeasureUpdate(B, lbl, incarnations.Keys, cont);
        }

        calc {
          StmtListMeasure(stmts) + ContinuationsMeasure(B);
        ==  // by assertion before `match`
          StmtMeasure(s0) + StmtListMeasure(cont) + ContinuationsMeasure(B);
        >  // by first assertion-by above
          StmtListMeasure([body, Exit(lbl)]) + StmtListMeasure(cont) + ContinuationsMeasure(B);
        >=  // by second assert-by above
          StmtListMeasure([body, Exit(lbl)]) + ContinuationsMeasure(B');
        }
      }
      WF.AboutBlockStmts(s0, b3);
      assert WF.StmtSeq([body, Exit(lbl)], b3);
      Process([body, Exit(lbl)], incarnations, B', o, b3);
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
    case VarDecl(_, _, _) => 1
    case Assign(_, _) => 1
    case Block(stmts) => StmtListMeasure(stmts)
    case Call(_, _) => 1 // TODO
    case Check(_) => 1
    case Assume(_) => 1
    case Assert(_) => 2
    case AForall(v, body) => 1 + StmtMeasure(body)
    case If(cases) => 1 + CaseMeasure(stmt, cases)
    case Loop(invariants, body) => 1 + StmtMeasure(body) // TODO
    case LabeledStmt(_, body) => 2 + StmtMeasure(body)
    case Exit(_) => 1
    case Probe(_) => 1
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
*************************/
}