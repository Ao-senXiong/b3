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
    var procs := b3.procedures;
    while procs != {} {
      var proc: Procedure :| proc in procs;
      procs := procs - {proc};

      :- CheckAExprs(proc.Pre);
      :- CheckAExprs(proc.Post);
      if proc.Body.Some? {
        :- CheckStmt(proc.Body.value);
      }
    }

    return Pass;
  }

  method CheckAExprs(aexprs: seq<AExpr>) returns (outcome: Outcome<string>) {
    for n := 0 to |aexprs| {
      match aexprs[n]
      case AExpr(e) =>
        outcome := TypeCheckAsBool(e);
      case AAssertion(s) =>
        :- CheckStmt(s);
    }
  }

  method TypeCheckAsBool(expr: Expr) returns (outcome: Outcome<string>) {
    var boolType := new Type(Types.BoolTypeName); // TODO: don't create new type here; use the existing bool type
    outcome := TypeCheckAs(expr, boolType);
  }

  method TypeCheckAs(expr: Expr, expectedType: Type) returns (outcome: Outcome<string>) {
    var r := CheckExpr(expr);
    if r.IsFailure() {
      return r.ToOutcome();
    }
    var typ := r.value;
    if typ.Name != expectedType.Name { // TODO: check reference equality (once bool/int has been figured out elsewhere in this file)
      return Fail("expect type '" + expectedType.Name + "', got type '" + typ.Name + "'");
    }
    return Pass;
  }

  method CheckStmt(stmt: Stmt) returns (outcome: Outcome<string>)
  {
    match stmt
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
    case Call(_, _) =>
      // TODO
      return Pass;
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
      return Pass;
    case Probe(expr) =>
      var r := CheckExpr(expr);
      if r.IsFailure() {
        return r.ToOutcome();
      }
      return Pass;
  }

/*
  method ResolveCallStmt(stmt: Raw.Stmt, rs: ResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires stmt.Call? && rs.Valid()
    ensures result.Success? ==> stmt.WellFormed(rs.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
  {
    var Call(name, args) := stmt;

    if name !in rs.procMap {
      return Failure("call to undeclared procedure: " + name);
    }
    var proc := rs.procMap[name];
    var rawProc :| rawProc in rs.b3.procedures && rawProc.name == name;
    assert |rawProc.parameters| == |proc.Parameters|;

    if |args| != |proc.Parameters| {
      return Failure("wrong number of arguments in call to procedure " + name);
    }
    assert |args| == |rawProc.parameters|;

    var aa := [];
    for n := 0 to |args|
      invariant forall i :: 0 <= i < n ==> args[i].mode == rawProc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> args[i].arg.WellFormed(rs.b3, ls.varMap.Keys)
    {
      if args[n].mode != proc.Parameters[n].mode {
        return Failure("mismatched parameter mode in call to procedure " + name);
      }
      var e :- ResolveExpr(args[n].arg, rs, ls.varMap);
      var ca;
      if args[n].mode == Raw.In {
        ca := InArgument(e);
      } else if !e.IdExpr? {
        return Failure(Printer.ParameterMode(args[n].mode) + "argument must be a variable");
      } else {
        ca := OutgoingArgument(args[n].mode == Raw.InOut, e.v);
      }
      aa := aa + [ca];
    }

    return Success(Call(proc, aa));
  }
*/

  method CheckExpr(expr: Expr) returns (r: Result<Type, string>) {
    match expr
    case BConst(_) =>
      var typ := new Type(Types.BoolTypeName); // TODO: don't create new type here; use the existing bool type
      return Success(typ);
    case IConst(_) =>
      var typ := new Type(Types.IntTypeName); // TODO: don't create new type here; use the existing int type
      return Success(typ);
    case IdExpr(v) =>
      return Success(v.typ);
  }
}