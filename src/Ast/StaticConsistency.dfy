module StaticConsistency {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast

  method CheckConsistent(program: Program) returns (outcome: Outcome<string>)
    requires program.WellFormed()
    ensures outcome.Pass? ==> Consistent(program)
  {
    for n := 0 to |program.procedures|
      invariant forall proc :: proc in program.procedures[..n] ==> ConsistentProc(proc)
    {
      :- CheckProcedure(program.procedures[n]);
    }
    return Pass;
  }

  predicate Consistent(b3: Program)
    requires b3.WellFormed()
    reads b3.functions, b3.procedures
  {
    forall proc <- b3.procedures :: ConsistentProc(proc)
  }

  predicate ConsistentProc(proc: Procedure)
    requires proc.WellFormed()
    reads proc
  {
    && (forall ae <- proc.Pre :: ConsistentAExpr(ae))
    && (forall ae <- proc.Post :: ConsistentAExpr(ae))
    && (proc.Body.Some? ==> ConsistentStmt(proc.Body.value))
  }

  predicate ConsistentAExpr(aexpr: AExpr)
    requires aexpr.WellFormed()
  {
    match aexpr
    case AExpr(e) => true
    case AAssertion(s) =>
      ConsistentStmt(s) && !ContainsNonAssertions(s)
  }

  predicate ConsistentStmt(stmt: Stmt)
    requires stmt.WellFormed()
  {
    match stmt
    case VarDecl(_, _, body) =>
      ConsistentStmt(body)
    case Assign(lhs, rhs) =>
      lhs.IsMutable()
    case Block(stmts) =>
      forall s <- stmts :: ConsistentStmt(s)
    case Call(proc, args) =>
      forall i :: 0 <= i < |args| ==> proc.Parameters[i].mode == args[i].CorrespondingMode()
    case Check(cond) => true
    case Assume(cond) => true
    case Assert(cond) => true
    case AForall(_, body) =>
      ConsistentStmt(body) && !ContainsNonAssertions(body)
    case Choose(branches) =>
      forall branch <- branches :: ConsistentStmt(branch)
    case Loop(invariants, body) =>
      && (forall inv <- invariants :: ConsistentAExpr(inv))
      && ConsistentStmt(body)
    case LabeledStmt(_, body) =>
      ConsistentStmt(body)
    case Exit(_) => true
    case Probe(expr) => true
  }

  predicate ContainsNonAssertions(stmt: Stmt) {
    match stmt
    case VarDecl(v, init, body) =>
      v.IsMutable() || init == None || ContainsNonAssertions(body)
    case Assign(_, _) => true
    case Block(stmts) =>
      exists stmt <- stmts :: ContainsNonAssertions(stmt)
    case Call(_, _) => true
    case Check(_) => false
    case Assume(_) => false
    case Assert(_) => false
    case AForall(_, body) =>
      ContainsNonAssertions(body)
    case Choose(branches) =>
      exists branch <- branches :: ContainsNonAssertions(branch)
    case Loop(_, _) => true
    case LabeledStmt(_, _) => true
    case Exit(_) => true
    case Probe(_) => false
  }

  method CheckProcedure(proc: Procedure) returns (outcome: Outcome<string>)
    requires proc.WellFormed()
    ensures outcome.Pass? ==> ConsistentProc(proc)
  {
    for n := 0 to |proc.Pre|
      invariant forall ae <- proc.Pre[..n] :: ConsistentAExpr(ae)
    {
      :- CheckAExpr(proc.Pre[n]);
    }
    for n := 0 to |proc.Post|
      invariant forall ae <- proc.Post[..n] :: ConsistentAExpr(ae)
    {
      :- CheckAExpr(proc.Post[n]);
    }
    if proc.Body.Some? {
      :- CheckStmt(proc.Body.value);
    }
    return Pass;
  }

  method CheckAExpr(aexpr: AExpr) returns (outcome: Outcome<string>)
    requires aexpr.WellFormed()
    ensures outcome.Pass? ==> ConsistentAExpr(aexpr)
  {
    match aexpr
    case AExpr(_) =>
      return Pass;
    case AAssertion(s) =>
      :- CheckStmt(s);
      :- CheckCanBeUsedInAssertion(s);
      return Pass;
  }

  method CheckStmt(stmt: Stmt) returns (outcome: Outcome<string>)
    requires stmt.WellFormed()
    ensures outcome.Pass? ==> ConsistentStmt(stmt)
  {
    match stmt {
      case VarDecl(_, _, body) =>
        :- CheckStmt(body);
      case Assign(lhs, _) =>
        if !lhs.IsMutable() {
          return Fail("assignment to immutable variable '" + lhs.name + "'");
        }
      case Block(stmts) =>
        for n := 0 to |stmts|
          invariant forall stmt <- stmts[..n] :: ConsistentStmt(stmt)
        {
          :- CheckStmt(stmts[n]);
        }
      case Call(proc, args) =>
        for n := 0 to |args|
          invariant forall i :: 0 <= i < n ==> proc.Parameters[i].mode == args[i].CorrespondingMode()
        {
          var formal := proc.Parameters[n];
          var actual := args[n];
          if formal.mode != actual.CorrespondingMode() {
            var a := formal.mode.ToString();
            var b := actual.CorrespondingMode().ToString();
            return Fail("incorrect parameter mode; expected " + a + "-parameter, got " + b + "-parameter");
          }
        }
      case Check(_) =>
      case Assume(_) =>
      case Assert(_) =>
      case AForall(_, body) =>
        :- CheckStmt(body);
        if ContainsNonAssertions(body) {
          return Fail("'forall' statement is not allowed to contain non-assertions");
        }
      case Choose(branches) =>
        for n := 0 to |branches|
          invariant forall branch <- branches[..n] :: ConsistentStmt(branch)
        {
          :- CheckStmt(branches[n]);
        }
      case Loop(invariants, body) =>
        for n := 0 to |invariants|
          invariant forall inv <- invariants[..n] :: ConsistentAExpr(inv)
        {
          :- CheckAExpr(invariants[n]);
        }
        :- CheckStmt(body);
      case LabeledStmt(_, body) =>
        :- CheckStmt(body);
      case Exit(_) =>
      case Probe(_) =>
    }
    return Pass;
  }

  method CheckCanBeUsedInAssertion(stmt: Stmt) returns (outcome: Outcome<string>)
    ensures outcome.Pass? ==> !ContainsNonAssertions(stmt)
  {
    match stmt {
      case VarDecl(v, init, body) =>
        if v.IsMutable() {
          return Fail("assertion is allowed to declare a mutable variable: '" + v.name + "'");
        }
        if init == None {
          return Fail("immutable variable declarations in assertions must have initializer: '" + v.name + "'");
        }
        :- CheckCanBeUsedInAssertion(body);
      case Block(stmts) =>
        for n := 0 to |stmts|
          invariant forall stmt <- stmts[..n] :: !ContainsNonAssertions(stmt)
        {
          :- CheckCanBeUsedInAssertion(stmts[n]);
        }
      case Check(_) =>
      case Assume(_) =>
      case Assert(_) =>
      case AForall(_, body) =>
        :- CheckCanBeUsedInAssertion(body);
      case Choose(branches) =>
        for n := 0 to |branches|
          invariant forall branch <- branches[..n] :: !ContainsNonAssertions(branch)
        {
          :- CheckCanBeUsedInAssertion(branches[n]);
        }
      case Probe(_) =>
      case _ =>
        return Fail("assertion can only contain assertion-compatible statements");
    }
    return Pass;
  }
}