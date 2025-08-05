module TypeChecker {
  export
    provides TypeCheck, TypeCorrect
    provides Wrappers, Ast

  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import opened Ast
  import Printer

  method TypeCheck(b3: Program) returns (outcome: Outcome<string>)
    requires b3.WellFormed()
    ensures outcome.Pass? ==> TypeCorrect(b3)
  {
    var r := FindType(Types.BoolTypeName, b3);
    :- TestSuccess(r);
    var boolType := r.value;

    r := FindType(Types.IntTypeName, b3);
    :- TestSuccess(r);
    var intType := r.value;

    var context := TypeCheckingContext(boolType, intType);

    var procs := b3.procedures;
    while procs != {}
      invariant forall proc <- b3.procedures - procs :: TypeCorrectProc(proc)
    {
      var proc: Procedure :| proc in procs;
      procs := procs - {proc};
      :- context.CheckProcedure(proc);
    }

    return Pass;
  }

  predicate TypeCorrect(b3: Program)
    reads b3.procedures
  {
    forall proc <- b3.procedures :: TypeCorrectProc(proc)
  }

  predicate TypeCorrectProc(proc: Procedure)
    reads proc
  {
    && (forall ae <- proc.Pre :: TypeCorrectAExpr(ae))
    && (forall ae <- proc.Post :: TypeCorrectAExpr(ae))
    && (proc.Body.Some? ==> TypeCorrectStmt(proc.Body.value))
  }

  predicate TypeCorrectAExpr(aexpr: AExpr) {
    match aexpr
    case AExpr(e) => TypeCorrectExpr(e)
    case AAssertion(s) => TypeCorrectStmt(s)
  }

  predicate TypeCorrectStmt(stmt: Stmt) {
    match stmt
    case VarDecl(variable, init, body) =>
      && (init.Some? ==> TypeCorrectExpr(init.value))
      && TypeCorrectStmt(body)
    case Assign(lhs, rhs) =>
      TypeCorrectExpr(rhs) && rhs.HasType(lhs.typ)
    case Block(stmts) =>
      forall s <- stmts :: TypeCorrectStmt(s)
    case Call(proc, args) =>
      forall arg <- args :: TypeCorrectCallArg(arg)
    case Check(cond) =>
      TypeCorrectExpr(cond)
    case Assume(cond) =>
      TypeCorrectExpr(cond)
    case Assert(cond) =>
      TypeCorrectExpr(cond)
    case AForall(_, body) =>
      TypeCorrectStmt(body)
    case Choice(branches) =>
      forall branch <- branches :: TypeCorrectStmt(branch)
    case Loop(invariants, body) =>
      && (forall inv <- invariants :: TypeCorrectAExpr(inv))
      && TypeCorrectStmt(body)
    case LabeledStmt(_, body) =>
      TypeCorrectStmt(body)
    case Exit(_) =>
      true
    case Probe(expr) =>
      TypeCorrectExpr(expr)
  }

  predicate TypeCorrectCallArg(arg: CallArgument) {
    match arg
    case InArgument(e) => TypeCorrectExpr(e)
    case OutgoingArgument(_, _) => true
  }

  predicate TypeCorrectExpr(expr: Expr) {
    match expr
    case BConst(_) => true
    case IConst(_) => true
    case IdExpr(_) => true
    case BinaryExpr(op, e0, e1) =>
      && TypeCorrectExpr(e0)
      && TypeCorrectExpr(e1)
      && match op {
        case Eq => true // TODO
      }
  }

  function TestSuccess<R, E>(r: Result<R, E>): Outcome<E> {
    if r.IsFailure() then Fail(r.error) else Pass
  }

  method FindType(typeName: string, b3: Program) returns (r: Result<Type, string>)
    ensures r.Success? ==> r.value.Name == typeName
  {
    if typ :| typ in b3.types && typ.Name == typeName {
      return Success(typ);
    } else {
      return Failure("cannot find built-in type '" + typeName + "'");
    }
  }

  datatype TypeCheckingContext = TypeCheckingContext(boolType: Type, intType: Type)
  {
    ghost predicate Valid() {
      && boolType.Name == Types.BoolTypeName
      && intType.Name == Types.IntTypeName
    }

    method CheckProcedure(proc: Procedure) returns (outcome: Outcome<string>)
      requires Valid() && proc.WellFormed()
      ensures outcome.Pass? ==> TypeCorrectProc(proc)
    {
      :- CheckAExprs(proc.Pre);
      :- CheckAExprs(proc.Post);
      if proc.Body.Some? {
        :- CheckStmt(proc.Body.value);
      }
      return Pass;
    }

    method CheckAExprs(aexprs: seq<AExpr>) returns (outcome: Outcome<string>)
      requires Valid() && forall ae <- aexprs :: ae.WellFormed()
      ensures outcome.Pass? ==> forall ae <- aexprs :: TypeCorrectAExpr(ae)
    {
      for n := 0 to |aexprs|
        invariant forall ae <- aexprs[..n] :: TypeCorrectAExpr(ae)
      {
        assert aexprs[n].WellFormed();
        match aexprs[n]
        case AExpr(e) =>
          outcome := TypeCheckAsBool(e);
          if outcome.IsFailure() {
            return Fail(outcome.error);
          }
        case AAssertion(s) =>
          assert aexprs decreases to s by {
            assert aexprs decreases to aexprs[n];
            assert aexprs[n] decreases to s;
          }
          :- CheckStmt(s);
      }
      return Pass;
    }

    method TypeCheckAsBool(expr: Expr) returns (outcome: Outcome<string>)
      requires Valid() && expr.WellFormed()
      ensures outcome.Pass? ==> TypeCorrectExpr(expr)
    {
      outcome := TypeCheckAs(expr, boolType);
    }

    method TypeCheckAs(expr: Expr, expectedType: Type) returns (outcome: Outcome<string>)
      requires Valid() && expr.WellFormed()
      ensures outcome.Pass? ==> TypeCorrectExpr(expr) && expr.HasType(expectedType)
    {
      var r := CheckExpr(expr);
      if r.IsFailure() {
        return r.ToOutcome();
      }
      var typ := r.value;
      outcome := ExpectType(typ, expectedType);
    }

    method ExpectType(typ: Type, expectedType: Type) returns (outcome: Outcome<string>)
      ensures outcome.Pass? ==> typ == expectedType
    {
      if typ != expectedType {
        return Fail("expect type '" + expectedType.Name + "', got type '" + typ.Name + "'");
      }
      return Pass;
    }

    method CheckStmt(stmt: Stmt) returns (outcome: Outcome<string>)
      requires Valid() && stmt.WellFormed()
      ensures outcome.Pass? ==> TypeCorrectStmt(stmt)
    {
      match stmt {
        case VarDecl(variable, init, body) =>
          if init.Some? {
            :- TypeCheckAs(init.value, variable.typ);
          }
          :- CheckStmt(body);
        case Assign(lhs, rhs) =>
          :- TypeCheckAs(rhs, lhs.typ);
        case Block(stmts) =>
          for n := 0 to |stmts|
            invariant forall s <- stmts[..n] :: TypeCorrectStmt(s)
          {
            :- CheckStmt(stmts[n]);
          }
        case Call(proc, args) =>
          for n := 0 to |args|
            invariant forall arg <- args[..n] :: TypeCorrectCallArg(arg)
          {
            var formal := proc.Parameters[n];
            match args[n]
            case InArgument(e) =>
              :- TypeCheckAs(e, formal.typ);
            case OutgoingArgument(_, arg) =>
              :- ExpectType(arg.typ, formal.typ);
          }
        case Check(cond) =>
          :- TypeCheckAsBool(cond);
        case Assume(cond) =>
          :- TypeCheckAsBool(cond);
        case Assert(cond) =>
          :- TypeCheckAsBool(cond);
        case AForall(_, body) =>
          :- CheckStmt(body);
        case Choice(branches) =>
          for n := 0 to |branches|
            invariant forall branch <- branches[..n] :: TypeCorrectStmt(branch)
          {
            :- CheckStmt(branches[n]);
          }
        case Loop(invariants, body) =>
          :- CheckAExprs(invariants);
          :- CheckStmt(body);
        case LabeledStmt(_, body) =>
          :- CheckStmt(body);
        case Exit(_) =>
        case Probe(expr) =>
          var r := CheckExpr(expr);
          if r.IsFailure() {
            return r.ToOutcome();
          }
      }
      return Pass;
    }

    method CheckExpr(expr: Expr) returns (r: Result<Type, string>)
      requires Valid() && expr.WellFormed()
      ensures r.Success? ==> TypeCorrectExpr(expr) && expr.HasType(r.value)
    {
      match expr
      case BConst(_) =>
        return Success(boolType);
      case IConst(_) =>
        return Success(intType);
      case IdExpr(v) =>
        return Success(v.typ);
      case BinaryExpr(op, e0, e1) =>
        var t0 :- CheckExpr(e0);
        var t1 :- CheckExpr(e1);
        match op {
          case Eq =>
            if t0 != t1 {
              return Result<Type, string>.Failure("operator == requires both arguments to have the same type; got '" + t0.Name + "' and '" + t1.Name + "'");
            }
        }
        return Success(boolType);
    }
  }
}