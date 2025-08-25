module Verifier {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import opened SolverExpr
  import RSolvers
  import StaticConsistency
  import AssignmentTargets
  import BC = BlockContinuations

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
    context := AssumeAExprs(proc.Post, preIncarnations, context, smtEngine);

    assert proc.Body.Some? ==> proc.Body.value.WellFormed();
    var body := if proc.Body.Some? then [proc.Body.value] else [];
    Process(body, bodyIncarnations, context, BC.Empty(), smtEngine);
    // TODO: postcondition checking should be appended to body, not checked separately

    // Check postcondition (TODO: should also vet postcondition)
    CheckAExprs(proc.Post, bodyIncarnations, context, smtEngine, "postcondition");
  }

  method CreateProcIncarnations(parameters: seq<Parameter>) returns (preIncarnations: Incarnations, bodyIncarnations: Incarnations)
    requires forall i :: 0 <= i < |parameters| ==> parameters[i].WellFormed()
  {
    preIncarnations, bodyIncarnations := Incarnations.Empty(), Incarnations.Empty();
    for i := 0 to |parameters| {
      var parameter := parameters[i];
      match parameter.mode
      case In =>
        var v := new SVar(parameter.name, Type2SType(parameter.typ));
        preIncarnations := preIncarnations.Set(parameter, v);
        bodyIncarnations := bodyIncarnations.Set(parameter, v);
      case InOut =>
        var vOld := new SVar(parameter.name + "%old", Type2SType(parameter.typ));
        preIncarnations := preIncarnations.Set(parameter, vOld);
        bodyIncarnations := bodyIncarnations.Set(parameter.oldInOut.value, vOld);
        bodyIncarnations := bodyIncarnations.Set(parameter, vOld);
      case out =>
        var v := new SVar(parameter.name, Type2SType(parameter.typ));
        bodyIncarnations := bodyIncarnations.Set(parameter, v);
    }
  }

  type RExpr = RSolvers.RExpr

  function Type2SType(typ: Type): SType {
    match typ
    case BoolType => SBool
    case IntType => SInt
    case UserType(decl) => SInt // TODO: SUserType(decl)
  }

  datatype Incarnations = Incarnations(nextSequenceCount: map<string, nat>, m: map<Variable, SVar>)
  {
    static function Empty(): Incarnations {
      Incarnations(map[], map[])
    }

    function Variables(): set<Variable> {
      m.Keys
    }

    // `Set` is intended to be used only during custom initializations of an Incarnations.
    function Set(v: Variable, sv: SVar): Incarnations {
      Incarnations(map[v.name := 0] + nextSequenceCount, m[v := sv])
    }

    method Update(v: Variable) returns (incarnations: Incarnations, x: SVar) {
      var name := v.name;
      var nextSequenceNumber;
      if name in nextSequenceCount.Keys {
        var n := nextSequenceCount[name];
        name := name + "%" + Int2String(n);
        nextSequenceNumber := n + 1;
      } else {
        nextSequenceNumber := 0;
      }
      x := new SVar(name, Type2SType(v.typ));
      incarnations := Incarnations(nextSequenceCount[v.name := nextSequenceNumber], m[v := x]);
    }

    function DomainRestrict(variables: set<Variable>): Incarnations {
      var m' := map v <- m.Keys | v in variables :: m[v];
      Incarnations(nextSequenceCount, m')
    }

    function REval(expr: Expr): RSolvers.RExpr
      requires expr.WellFormed()
    {
      match expr
      case BLiteral(value) => RExpr.Boolean(value)
      case ILiteral(value) => RExpr.Integer(value)
      case CustomLiteral(s, typ) => RExpr.CustomLiteral(s, Type2SType(typ))
      case IdExpr(v) =>
        assume {:axiom} v in m; // TODO: it would be nice to be able to keep the original variable if there's no incarnation; that would be the case for the bound variable in a let expression or quantifier
        RExpr.Id(m[v])
      case OperatorExpr(op, args) =>
        var rArgs := REvalList(args);
        match op {
          case IfThenElse =>
            RExpr.IfThenElse(rArgs[0], rArgs[1], rArgs[2])
          case Neq =>
            var eq := RExpr.FuncAppl(RExpr.OperatorToString(Operator.Eq), rArgs);
            RExpr.FuncAppl(RExpr.OperatorToString(Operator.LogicalNot), [eq])
          case _ =>
            RExpr.FuncAppl(RExpr.OperatorToString(op), rArgs)
        }
      case FunctionCallExpr(func, args) =>
        var rArgs := REvalList(args);
        RExpr.FuncAppl(func.Name, rArgs)
      case LabeledExpr(_, body) =>
        // TODO: do something with the label
        REval(body)
      case LetExpr(v, rhs, body) =>
        RExpr.Boolean(true) //RExpr.LetExpr(v, REval(rhs), REval(body)) // TODO: this requires RExpr and Expr have the same Variables.
      case QuantifierExpr(univ, v, triggers, body) =>
        var trs := REvalTriggers(triggers);
        var b := REval(body);
        RExpr.Boolean(true) //RExpr.QuantifierExpr(univ, v, trs, b) // TODO: this requires RExpr and Expr have the same Variables.
    }

    function REvalList(exprs: seq<Expr>): seq<RSolvers.RExpr>
      requires forall expr <- exprs :: expr.WellFormed()
      ensures |REvalList(exprs)| == |exprs|
    {
      if exprs == [] then
        []
      else
        [REval(exprs[0])] + REvalList(exprs[1..])
    }

    function REvalTriggers(triggers: seq<Trigger>): seq<seq<RSolvers.RExpr>>
      requires forall tr <- triggers :: tr.WellFormed()
    {
      if triggers == [] then
        []
      else
        assert triggers[0].WellFormed();
        [REvalList(triggers[0].exprs)] + REvalTriggers(triggers[1..])
    }
  }

  method Process(stmts: seq<Stmt>, incarnations_in: Incarnations, context_in: RSolvers.RContext, B: BC.T, smtEngine: RSolvers.REngine)
    requires forall stmt <- stmts :: stmt.WellFormed()
    requires BC.Valid(B)
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
    decreases BC.StmtSeqMeasure(stmts) + BC.ContinuationsMeasure(B)
  {
    if stmts == [] {
      return;
    }

    var incarnations, context := incarnations_in, context_in;
    var stmt, cont := stmts[0], stmts[1..];
    assert stmt.WellFormed();
    BC.StmtMeasureSplit(stmts);
    match stmt
    case VarDecl(v, init, body) =>
      var sv;
      incarnations, sv := incarnations.Update(v);
      if init.Some? {
        var sRhs := incarnations.REval(init.value);
        context := RSolvers.Extend(context, RExpr.Eq(RExpr.Id(sv), sRhs));
      }
      BC.StmtMeasurePrepend(body, cont);
      Process([body] + cont, incarnations, context, B, smtEngine);
    case Assign(lhs, rhs) =>
      var sRhs := incarnations.REval(rhs);
      var sLhs;
      incarnations, sLhs := incarnations.Update(lhs);
      context := RSolvers.Extend(context, RExpr.Eq(RExpr.Id(sLhs), sRhs));
      Process(cont, incarnations, context, B, smtEngine);
    case Block(stmts) =>
      BC.AboutStmtSeqMeasureConcat(stmts, cont);
      Process(stmts + cont, incarnations, context, B, smtEngine);
    case Call(_, _) =>
      print "UNHANDLED STATEMENT: Call\n"; // TODO
      Process(cont, incarnations, context, B, smtEngine);
    case Check(cond) =>
      ProveAndReport(context, incarnations.REval(cond), "check", cond, smtEngine);
      Process(cont, incarnations, context, B, smtEngine);
    case Assume(cond) =>
      context := RSolvers.Extend(context, incarnations.REval(cond));
      Process(cont, incarnations, context, B, smtEngine);
    case Assert(cond) =>
      var e := incarnations.REval(cond);
      ProveAndReport(context, e, "assert", cond, smtEngine);
      context := RSolvers.Extend(context, e);
      Process(cont, incarnations, context, B, smtEngine);
    case AForall(v, body) =>
      var bodyIncarnations, _ := incarnations.Update(v);
      BC.AboutStmtSeqMeasureSingleton(body);
      Process([body], bodyIncarnations, context, B, smtEngine);

      expect !StaticConsistency.ContainsNonAssertions(stmt); // TODO: prove that this follows from the AForall statement satisfying its static checks
      var L := Learn(stmt);
      context := RSolvers.Extend(context, incarnations.REval(L));
      Process(cont, incarnations, context, B, smtEngine);
    case Choice(branches) =>
      for i := 0 to |branches|
        invariant smtEngine.Valid()
      {
        BC.StmtSeqElement(branches, i);
        BC.StmtMeasurePrepend(branches[i], cont);
        Process([branches[i]] + cont, incarnations, context, B, smtEngine);
      }
    case Loop(invariants, body) =>
      // `cont` is ignored, since a `loop` never has any normal exit
      ProcessLoop(stmt, incarnations, context, B, smtEngine);
    case LabeledStmt(lbl, body) =>
      var B' := B[lbl := BC.Continuation(incarnations.Variables(), cont)];
      BC.AboutContinuationsMeasureUpdate(B, lbl, incarnations.Variables(), cont);
      BC.StmtPairMeasure(body, Exit(lbl));
      Process([body, Exit(lbl)], incarnations, context, B', smtEngine);
    case Exit(lbl) =>
      expect lbl in B, lbl.Name; // TODO
      var c := B[lbl];
      var variablesInScope, cont := c.variablesInScope, c.continuation;
      var incarnations' := incarnations.DomainRestrict(variablesInScope);
      var B0 := B - {lbl};
      assert B == B0[lbl := BC.Continuation(variablesInScope, cont)];
      assert BC.ContinuationsMeasure(B) >= BC.StmtSeqMeasure(cont) + BC.ContinuationsMeasure(B0) by {
        BC.AboutContinuationsMeasure(B0, lbl, variablesInScope, cont);
      }
      Process(cont, incarnations', context, B0, smtEngine);
    case Probe(e) =>
      context := RSolvers.Record(context, incarnations.REval(e));
      Process(cont, incarnations, context, B, smtEngine);
  }

  method ProcessLoop(stmt: Stmt, incarnations_in: Incarnations, context_in: RSolvers.RContext, B: BC.T, smtEngine: RSolvers.REngine)
    requires stmt.Loop? && stmt.WellFormed() && BC.Valid(B) && smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
    decreases BC.StmtMeasure(stmt) + BC.ContinuationsMeasure(B), 0
  {
    var incarnations, context := incarnations_in, context_in;

    // Check invariants on entry
    CheckAExprs(stmt.invariants, incarnations, context, smtEngine, "invariant on entry");

    // Havoc the assignment targets of the loop body
    var assignmentTargets := AssignmentTargets.Compute(stmt.body);
    while assignmentTargets != {}
      invariant smtEngine.Valid()
    {
      var v :| v in assignmentTargets;
      assignmentTargets := assignmentTargets - {v};
      var sv;
      incarnations, sv := incarnations.Update(v);
    }

    // TODO: should also vet the invariants

    // Assume invariants
    context := AssumeAExprs(stmt.invariants, incarnations, context, smtEngine);
    // Process body
    BC.AboutStmtSeqMeasureSingleton(stmt.body);
    Process([stmt.body], incarnations, context, B, smtEngine);

    // TODO: postcondition checking should be appended to body, not checked separately

    // Check that invariants are maintained
    CheckAExprs(stmt.invariants, incarnations, context, smtEngine, "invariant maintained");
  }

  method CheckAExprs(aexprs: seq<AExpr>, incarnations: Incarnations, context: RSolvers.RContext, smtEngine: RSolvers.REngine, errorText: string)
    requires forall ae <- aexprs :: ae.WellFormed()
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    for i := 0 to |aexprs|
      invariant smtEngine.Valid()
    {
      assert aexprs[i].WellFormed();
      match aexprs[i]
      case AExpr(e) =>
        ProveAndReport(context, incarnations.REval(e), errorText, e, smtEngine);
      case _ => // TODO
    }
  }

  method AssumeAExprs(aexprs: seq<AExpr>, incarnations: Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine)
      returns (context: RSolvers.RContext)
    requires forall ae <- aexprs :: ae.WellFormed()
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    context := context_in;
    for i := 0 to |aexprs|
      invariant smtEngine.Valid()
    {
      assert aexprs[i].WellFormed();
      match aexprs[i]
      case AExpr(e) =>
        context := RSolvers.Extend(context, incarnations.REval(e));
      case _ => // TODO
    }
  }

  // `errorReportingInfo` is currently an expression that, together with `errorText`, gets printed
  // if `context ==> expr` cannot be proved by `smtEngine`.
  // TODO: This should be improved to instead use source locations.
  method ProveAndReport(context: RSolvers.RContext, expr: RExpr, errorText: string, errorReportingInfo: Expr, smtEngine: RSolvers.REngine)
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    var result := smtEngine.Prove(context, expr);
    match result
    case Proved =>
    case Unproved(reason) =>
      print "Error: Failed to prove ", errorText, " ", errorReportingInfo.ToString(), "\n";
      print "Reason: ", reason, "\n";
  }

  function Learn(stmt: Stmt): Expr
    requires stmt.WellFormed() && !StaticConsistency.ContainsNonAssertions(stmt)
    ensures Learn(stmt).WellFormed()
  {
    match stmt
    case VarDecl(v, Some(rhs), body) =>
      Expr.CreateLet(v, rhs, Learn(body))
    case Block(stmts) =>
      var ll := SeqMap(stmts, (s: Stmt) requires s in stmts => Learn(s));
      Expr.CreateBigAnd(ll)
    case Check(_) =>
      Expr.CreateTrue()
    case Assume(e) =>
      e
    case Assert(e) =>
      e
    case AForall(v, body) =>
      Expr.CreateForall(v, Learn(body))
    case Choice(branches) =>
      var ll := SeqMap(branches, (s: Stmt) requires s in branches => Learn(s));
      Expr.CreateBigOr(ll)
    case Probe(_) =>
      Expr.CreateTrue()
  }
}