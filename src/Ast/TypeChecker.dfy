module TypeChecker {
  export
    provides TypeCheck
    provides Wrappers, Ast

  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import opened Ast
  import Printer

  method TypeCheck(b3: Program) returns (outcome: Outcome<string>)
    // TODO: add postcondition that describes what a properly typed program is
  {
    var r := FindType(Types.BoolTypeName, b3);
    :- TestSuccess(r);
    var boolType := r.value;

    r := FindType(Types.IntTypeName, b3);
    :- TestSuccess(r);
    var intType := r.value;

    var context := TypeCheckingContext(boolType, intType);

    var procs := b3.procedures;
    while procs != {} {
      var proc: Procedure :| proc in procs;
      procs := procs - {proc};
      :- context.CheckProcedure(proc);
    }

    return Pass;
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
      requires Valid()
    {
      :- CheckAExprs(proc.Pre);
      :- CheckAExprs(proc.Post);
      if proc.Body.Some? {
        :- CheckStmt(proc.Body.value);
      }
      return Pass;
    }

    method CheckAExprs(aexprs: seq<AExpr>) returns (outcome: Outcome<string>) {
      for n := 0 to |aexprs| {
        match aexprs[n]
        case AExpr(e) =>
          outcome := TypeCheckAsBool(e);
        case AAssertion(s) =>
          assert aexprs decreases to s by {
            assert aexprs decreases to aexprs[n];
            assert aexprs[n] decreases to s;
          }
          :- CheckStmt(s);
      }
      return Pass;
    }

    method TypeCheckAsBool(expr: Expr) returns (outcome: Outcome<string>) {
      outcome := TypeCheckAs(expr, boolType);
    }

    method TypeCheckAs(expr: Expr, expectedType: Type) returns (outcome: Outcome<string>) {
      var r := CheckExpr(expr);
      if r.IsFailure() {
        return r.ToOutcome();
      }
      var typ := r.value;
      outcome := ExpectType(typ, expectedType);
    }

    method ExpectType(typ: Type, expectedType: Type) returns (outcome: Outcome<string>) {
      if typ != expectedType {
        return Fail("expect type '" + expectedType.Name + "', got type '" + typ.Name + "'");
      }
      return Pass;
    }

    method CheckStmt(stmt: Stmt) returns (outcome: Outcome<string>)
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
          for n := 0 to |stmts| {
            :- CheckStmt(stmts[n]);
          }
        case Call(proc, args) =>
          expect |proc.Parameters| == |args|; // TODO: this follows from successful resolution
          for n := 0 to |args| {
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
        case If(cases) =>
          for n := 0 to |cases| {
            :- TypeCheckAsBool(cases[n].cond);
            :- CheckStmt(cases[n].body);
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

    method CheckExpr(expr: Expr) returns (r: Result<Type, string>) {
      match expr
      case BConst(_) =>
        return Success(boolType);
      case IConst(_) =>
        return Success(intType);
      case IdExpr(v) =>
        return Success(v.typ);
    }
  }
}