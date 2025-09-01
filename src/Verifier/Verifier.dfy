module Verifier {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import opened SolverExpr
  import I = Incarnations
  import RSolvers
  import StaticConsistency
  import AssignmentTargets
  import BC = BlockContinuations
  import CLI = CommandLineOptions

  export
    provides Verify
    provides Ast, CLI, StaticConsistency

  method Verify(b3: Ast.Program, cli: CLI.CliResult)
    requires b3.WellFormed() && StaticConsistency.Consistent(b3)
  {
    var typeMap := map[];
    var types := b3.types;
    while types != {}
      decreases types
    {
      var typ: Types.TypeDecl :| typ in types;
      types := types - {typ};
      var t := new STypeDecl(typ.Name);
      typeMap := typeMap[typ := t];
    }

    var functionMap := map[];
    var funcs := b3.functions;
    while funcs != {}
      decreases funcs
    {
      var func: Function :| func in funcs;
      funcs := funcs - {func};
      var inputTypes := SeqMap(func.Parameters, (parameter: FParameter) => I.DeclMappings.Type2STypeWithMap(parameter.typ, typeMap));
      var f := new SVar.Function(func.Name, inputTypes, I.DeclMappings.Type2STypeWithMap(func.ResultType, typeMap));
      functionMap := functionMap[func := f];
    }

    var declMap := I.DeclMappings(typeMap, functionMap);
    var procs := b3.procedures;
    while procs != {}
    {
      var proc: Procedure :| proc in procs;
      procs := procs - {proc};

      print "Verifying ", proc.Name, " ...\n";
      VerifyProcedure(proc, declMap, cli);
    }
  }

  method VerifyProcedure(proc: Ast.Procedure, declMap: I.DeclMappings, cli: CLI.CliResult)
    requires proc.WellFormed() && StaticConsistency.ConsistentProc(proc)
  {
    var smtEngine := RSolvers.CreateEngine(cli);
    var context := RSolvers.CreateEmptyContext();

    // Create incarnations for parameters in the pre-state
    var preIncarnations, bodyIncarnations := CreateProcIncarnations(proc.Parameters, declMap);

    // Assume precondition (TODO: should also vet precondition)
    context := AssumeAExprs(proc.Post, preIncarnations, context, smtEngine);

    assert proc.Body.Some? ==> proc.Body.value.WellFormed();
    var body := if proc.Body.Some? then [proc.Body.value] else [];
    Process(body, bodyIncarnations, context, BC.Empty(), smtEngine);
    // TODO: postcondition checking should be appended to body, not checked separately

    // Check postcondition (TODO: should also vet postcondition)
    CheckAExprs(proc.Post, bodyIncarnations, context, smtEngine, "postcondition");
  }

  method CreateProcIncarnations(parameters: seq<Parameter>, declMap: I.DeclMappings) returns (preIncarnations: I.Incarnations, bodyIncarnations: I.Incarnations)
    requires forall i :: 0 <= i < |parameters| ==> parameters[i].WellFormed()
  {
    preIncarnations, bodyIncarnations := I.Incarnations.Empty(declMap), I.Incarnations.Empty(declMap);
    for i := 0 to |parameters| {
      var parameter := parameters[i];
      match parameter.mode
      case In =>
        var v := new SVar(parameter.name, declMap.Type2SType(parameter.typ));
        preIncarnations := preIncarnations.Set(parameter, v);
        bodyIncarnations := bodyIncarnations.Set(parameter, v);
      case InOut =>
        var vOld := new SVar(parameter.name + "%old", declMap.Type2SType(parameter.typ));
        preIncarnations := preIncarnations.Set(parameter, vOld);
        bodyIncarnations := bodyIncarnations.Set(parameter.oldInOut.value, vOld);
        bodyIncarnations := bodyIncarnations.Set(parameter, vOld);
      case out =>
        var v := new SVar(parameter.name, declMap.Type2SType(parameter.typ));
        bodyIncarnations := bodyIncarnations.Set(parameter, v);
    }
  }

  method Process(stmts: seq<Stmt>, incarnations_in: I.Incarnations, context_in: RSolvers.RContext, B: BC.T, smtEngine: RSolvers.REngine)
    requires forall stmt <- stmts :: stmt.WellFormed() && StaticConsistency.ConsistentStmt(stmt)
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
        context := RSolvers.Extend(context, RSolvers.RExpr.Eq(RSolvers.RExpr.Id(sv), sRhs));
      }
      BC.StmtMeasurePrepend(body, cont);
      Process([body] + cont, incarnations, context, B, smtEngine);
    case Assign(lhs, rhs) =>
      var sRhs := incarnations.REval(rhs);
      var sLhs;
      incarnations, sLhs := incarnations.Update(lhs);
      context := RSolvers.Extend(context, RSolvers.RExpr.Eq(RSolvers.RExpr.Id(sLhs), sRhs));
      Process(cont, incarnations, context, B, smtEngine);
    case Block(stmts) =>
      BC.AboutStmtSeqMeasureConcat(stmts, cont);
      Process(stmts + cont, incarnations, context, B, smtEngine);
    case Call(_, _) =>
      print "UNHANDLED STATEMENT: Call\n"; // TODO
      Process(cont, incarnations, context, B, smtEngine);
    case Check(cond) =>
      var rCond := incarnations.REval(cond);
      ProveAndReport(context, rCond, "check", cond, smtEngine);
      Process(cont, incarnations, context, B, smtEngine);
    case Assume(cond) =>
      var rCond := incarnations.REval(cond);
      context := RSolvers.Extend(context, rCond);
      Process(cont, incarnations, context, B, smtEngine);
    case Assert(cond) =>
      var rCond := incarnations.REval(cond);
      ProveAndReport(context, rCond, "assert", cond, smtEngine);
      context := RSolvers.Extend(context, rCond);
      Process(cont, incarnations, context, B, smtEngine);
    case AForall(v, body) =>
      var bodyIncarnations, _ := incarnations.Update(v);
      BC.AboutStmtSeqMeasureSingleton(body);
      Process([body], bodyIncarnations, context, B, smtEngine);
      assert !StaticConsistency.ContainsNonAssertions(stmt);
      var L := Learn(stmt);
      var rL := incarnations.REval(L);
      context := RSolvers.Extend(context, rL);
      Process(cont, incarnations, context, B, smtEngine);
    case Choose(branches) =>
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
      var B' := BC.Add(B, lbl, incarnations.Variables(), cont);
      BC.AboutContinuationsMeasureAdd(B, lbl, incarnations.Variables(), cont);
      BC.StmtPairMeasure(body, Exit(lbl));
      Process([body, Exit(lbl)], incarnations, context, B', smtEngine);
    case Exit(lbl) =>
      expect lbl in B, lbl.Name; // TODO
      var c := BC.Get(B, lbl);
      var variablesInScope, cont := c.variablesInScope, c.continuation;
      var incarnations' := incarnations.DomainRestrict(variablesInScope);
      var B0 := BC.Remove(B, lbl);
      assert B == B0[lbl := BC.Continuation(variablesInScope, cont)];
      assert B == BC.Add(B0, lbl, variablesInScope, cont);
      assert BC.ContinuationsMeasure(B) >= BC.StmtSeqMeasure(cont) + BC.ContinuationsMeasure(B0) by {
        BC.AboutContinuationsMeasure(B0, lbl, variablesInScope, cont);
      }
      Process(cont, incarnations', context, B0, smtEngine);
    case Probe(e) =>
      var rExpr := incarnations.REval(e);
      context := RSolvers.Record(context, rExpr, incarnations.Type2SType(e.ExprType()));
      Process(cont, incarnations, context, B, smtEngine);
  }

  method ProcessLoop(stmt: Stmt, incarnations_in: I.Incarnations, context_in: RSolvers.RContext, B: BC.T, smtEngine: RSolvers.REngine)
    requires stmt.Loop? && stmt.WellFormed() && StaticConsistency.ConsistentStmt(stmt)
    requires BC.Valid(B) && smtEngine.Valid()
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

  method CheckAExprs(aexprs: seq<AExpr>, incarnations: I.Incarnations, context: RSolvers.RContext, smtEngine: RSolvers.REngine, errorText: string)
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
        var rExpr := incarnations.REval(e);
        ProveAndReport(context, rExpr, errorText, e, smtEngine);
      case _ => // TODO
    }
  }

  method AssumeAExprs(aexprs: seq<AExpr>, incarnations: I.Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine)
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
        var rExpr := incarnations.REval(e);
        context := RSolvers.Extend(context, rExpr);
      case _ => // TODO
    }
  }

  // `errorReportingInfo` is currently an expression that, together with `errorText`, gets printed
  // if `context ==> expr` cannot be proved by `smtEngine`.
  // TODO: This should be improved to instead use source locations.
  method ProveAndReport(context: RSolvers.RContext, expr: RSolvers.RExpr, errorText: string, errorReportingInfo: Expr, smtEngine: RSolvers.REngine)
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
    case Choose(branches) =>
      var ll := SeqMap(branches, (s: Stmt) requires s in branches => Learn(s));
      Expr.CreateBigOr(ll)
    case Probe(_) =>
      Expr.CreateTrue()
  }
}