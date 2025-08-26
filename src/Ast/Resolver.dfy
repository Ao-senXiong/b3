module Resolver {
  export
    provides Resolve
    provides Wrappers, Raw, Ast

  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import Raw = RawAst
  import opened Ast
  import Printer

  method Resolve(b3: Raw.Program) returns (r: Result<Ast.Program, string>)
    ensures r.Success? ==> b3.WellFormed() && r.value.WellFormed()
  {
    var typeMap: map<string, TypeDecl> := map[];
    for n := 0 to |b3.types|
      // typeMap maps user-defined types seen so far to distinct type-declaration objects
      invariant typeMap.Keys == set typename <- b3.types[..n]
      invariant MapIsInjective(typeMap)
      // typeMap organizes type-declaration objects correctly according to their names
      invariant forall typename <- typeMap.Keys :: typeMap[typename].Name == typename
      // no user-defined type seen so far uses the name of a built-in type
      invariant forall typename <- b3.types[..n] :: typename !in BuiltInTypes
      // the user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.types[i] != b3.types[j]
    {
      var name := b3.types[n];
      if name in BuiltInTypes {
        return Failure("user-defined type is not allowed to have the name of a built-in type: " + name);
      } else if name in typeMap.Keys {
        return Failure("duplicate type name: " + name);
      }
      var decl := new TypeDecl(name);
      typeMap := typeMap[name := decl];
    }

    var procMap: map<string, Procedure> := map[];
    for n := 0 to |b3.procedures|
      // procMap maps the user-defined procedures seen so far to distinct and fresh procedure-declaration objects
      invariant procMap.Keys == set proc <- b3.procedures[..n] :: proc.name
      invariant MapIsInjective(procMap)
      invariant forall name <- procMap :: fresh(procMap[name])
      // procMap organizes procedure-declaration objects correctly according to their names
      invariant forall procname <- procMap.Keys :: procMap[procname].Name == procname
      // user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.procedures[i].name != b3.procedures[j].name
      // the procedures seen so far are well-formed
      invariant forall proc <- b3.procedures[..n] :: proc.SignatureWellFormed(b3) && procMap[proc.name].SignatureWellFormed(proc)
    {
      var proc := b3.procedures[n];
      var name := proc.name;
      if name in procMap.Keys {
        return Failure("duplicate procedure name: " + name);
      }
      var rproc :- ResolveProcedureSignature(proc, b3, typeMap);
      procMap := procMap[name := rproc];
    }

    var rs := ResolverState(b3, typeMap, procMap);
    for n := 0 to |b3.procedures|
      invariant forall proc <- b3.procedures :: proc.SignatureWellFormed(b3) && procMap[proc.name].SignatureWellFormed(proc)
      invariant forall proc <- b3.procedures[..n] :: proc.WellFormed(b3)
      invariant forall proc <- b3.procedures[..n] :: procMap[proc.name].WellFormed()
    {
      var proc := b3.procedures[n];
      var _ :- ResolveProcedure(proc, procMap[proc.name], rs);
    }

    var r3 := Program(typeMap.Values, procMap.Values);

    return Success(r3);
  }

  method ResolveProcedureSignature(proc: Raw.Procedure, b3: Raw.Program, typeMap: map<string, TypeDecl>) returns (r: Result<Procedure, string>)
    requires forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap
    ensures r.Success? ==> proc.SignatureWellFormed(b3)
    ensures r.Success? ==> fresh(r.value) && r.value.SignatureWellFormed(proc)
  {
    var paramMap: map<string, Variable> := map[];
    var formals: seq<Parameter> := [];
    for n := 0 to |proc.parameters|
      invariant forall p <- proc.parameters[..n] :: Raw.LegalVariableName(p.name) && b3.IsType(p.typ)
      invariant forall i, j :: 0 <= i < j < n ==> proc.parameters[i].name != proc.parameters[j].name
      invariant paramMap.Keys ==
        (set p <- proc.parameters[..n] :: p.name) +
        (set p <- proc.parameters[..n] | p.mode == Raw.InOut :: Raw.OldName(p.name))
      invariant |formals| == n
      invariant forall i :: 0 <= i < n ==> formals[i] == paramMap[proc.parameters[i].name]
      invariant forall i :: 0 <= i < n ==> formals[i].name == proc.parameters[i].name
      invariant forall i :: 0 <= i < n ==> formals[i].mode == proc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> (formals[i].oldInOut.Some? <==> proc.parameters[i].mode == Raw.InOut)
    {
      var p := proc.parameters[n];
      if !Raw.LegalVariableName(p.name) {
        return Failure("illegal parameter name: " + p.name);
      }
      if p.name in paramMap {
        return Failure("duplicate parameter name: " + p.name);
      }
      var typ :- ResolveType(p.typ, typeMap);

      var oldInOut;
      if p.mode == Raw.InOut {
        var v := new LocalVariable(Raw.OldName(p.name), false, typ);
        oldInOut := Some(v);
        paramMap := paramMap[Raw.OldName(p.name) := v];
      } else {
        oldInOut := None;
      }

      var formal := new Parameter(p.name, p.mode, typ, oldInOut);
      paramMap := paramMap[p.name := formal];
      formals := formals + [formal];
    }

    var rproc := new Procedure(proc.name, formals);
    return Success(rproc);
  }

  method ResolveType(typename: string, typeMap: map<string, TypeDecl>) returns (r: Result<Type, string>)
    ensures r.Success? ==> typename in BuiltInTypes || typename in typeMap
  {
    if typename == BoolTypeName {
      return Success(BoolType);
    } else if typename == IntTypeName {
      return Success(IntType);
    }

    if typename !in typeMap {
      return Failure("unknown type: " + typename);
    }
    return Success(UserType(typeMap[typename]));
  }

  datatype ResolverState = ResolverState(b3: Raw.Program, typeMap: map<string, TypeDecl>, procMap: map<string, Procedure>)
  {
    ghost predicate Valid() {
      && (forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap)
      && (forall procname <- procMap :: exists proc <- b3.procedures :: proc.name == procname)
      && (forall rawProc <- b3.procedures ::
            rawProc.name in procMap &&
            var proc := procMap[rawProc.name];
            && |rawProc.parameters| == |proc.Parameters|
            && (forall i :: 0 <= i < |rawProc.parameters| ==> rawProc.parameters[i].mode == proc.Parameters[i].mode)
         )
    }
  }

  datatype LocalResolverState = LocalResolverState(
    varMap: map<string, Variable>,
    labelMap: map<string, Label>,
    loopLabel: Option<Label>,
    returnLabel: Label)
  {
    function AddVariable(name: string, v: Variable): LocalResolverState
      ensures AddVariable(name, v).varMap.Keys == varMap.Keys + {name}
    {
      this.(varMap := varMap[name := v])
    }

    function FindLabel(name: string): Result<Label, string> {
      if name in labelMap then
        Success(labelMap[name])
      else
        Failure("undeclared exit label: " + name)
    }

    function LabelSet(): set<string>
      ensures labelMap == map[] ==> LabelSet() == {}
    {
      labelMap.Keys
    }

    function AddLabel(name: string, lbl: Label): LocalResolverState
      ensures AddLabel(name, lbl).labelMap.Keys == labelMap.Keys + {name}
    {
      this.(labelMap := labelMap[name := lbl])
    }

    method GenerateLoopLabel() returns (lbl: Label, ls: LocalResolverState)
      ensures ls.varMap.Keys == varMap.Keys
      ensures ls.LabelSet() == LabelSet()
      ensures ls.loopLabel.Some?
    {
      lbl := new Label("loop");
      ls := this.(loopLabel := Some(lbl));
    }
  }

  method ResolveProcedure(proc: Raw.Procedure, rproc: Procedure, rs: ResolverState) returns (r: Result<(), string>)
    requires proc.SignatureWellFormed(rs.b3) && rproc.SignatureWellFormed(proc) && rs.Valid()
    modifies rproc
    ensures r.Success? ==> proc.WellFormed(rs.b3) && rproc.WellFormed()
  {
    var formals := rproc.Parameters;
    var n := |formals|;
    assert forall formal: Parameter <- formals :: Raw.LegalVariableName(formal.name);
    assert forall i, j :: 0 <= i < j < n ==> formals[i].name != formals[j].name;
    forall i, j | 0 <= i < j < n
      ensures Raw.OldName(formals[i].name) != Raw.OldName(formals[j].name)
    {
      var a, b := formals[i].name, formals[j].name;
      assert a != b;
      assert Raw.OldName(a)[|Raw.OldPrefix|..] == a;
      assert Raw.OldName(a) != Raw.OldName(b);
    }
    var paramMap :=
      (map formal <- rproc.Parameters :: formal.name := formal) +
      (map formal <- rproc.Parameters | formal.oldInOut.Some? :: Raw.OldName(formal.name) := formal.oldInOut.value);

    assert n == |proc.parameters|;
    assert forall i :: 0 <= i < n ==> formals[i].name == proc.parameters[i].name;
    assert forall i :: 0 <= i < n ==> (formals[i].oldInOut.Some? <==> proc.parameters[i].mode == Raw.InOut);

    var preScope := set p <- proc.parameters | p.mode.IsIncoming() :: p.name;
    var postScope := (set p <- proc.parameters :: p.name) + (set p <- proc.parameters | p.mode == Raw.InOut :: Raw.OldName(p.name));

    var returnLabel := new Label("return");

    var preVariables := MapProject(paramMap, preScope);
    assert preVariables.Keys == preScope;
    var pre :- ResolveAExprs(proc.pre, rs, LocalResolverState(preVariables, map[], None, returnLabel));

    var postVariables := MapProject(paramMap, postScope);
    assert postVariables.Keys == postScope;
    var ls := LocalResolverState(postVariables, map[], None, returnLabel);
    var post :- ResolveAExprs(proc.post, rs, ls);

    var body;
    if proc.body == None {
      body := None;
    } else {
      var b :- ResolveStmt(proc.body.value, rs, ls);
      body := Some(LabeledStmt(returnLabel, b));
    }

    rproc.Pre := pre;
    rproc.Post := post;
    rproc.Body := body;
    return Success(());
  }

  method ResolveAExprs(aexprs: seq<Raw.AExpr>, rs: ResolverState, ls: LocalResolverState) returns (r: Result<seq<AExpr>, string>)
    requires rs.Valid()
    ensures r.Success? ==> forall ae <- aexprs :: ae.WellFormed(rs.b3, ls.varMap.Keys)
    ensures r.Success? ==> forall ae <- r.value :: ae.WellFormed()
  {
    var result := [];
    for n := 0 to |aexprs|
      invariant forall ae <- aexprs[..n] :: ae.WellFormed(rs.b3, ls.varMap.Keys)
      invariant forall ae: AExpr <- result :: ae.WellFormed()
    {
      var ae :- ResolveAExpr(aexprs[n], rs, ls);
      result := result + [ae];
    }
    return Success(result);
  }

  method ResolveAExpr(aexpr: Raw.AExpr, rs: ResolverState, ls: LocalResolverState) returns (r: Result<AExpr, string>)
    requires rs.Valid()
    ensures r.Success? ==> aexpr.WellFormed(rs.b3, ls.varMap.Keys)
    ensures r.Success? ==> r.value.WellFormed()
  {
    match aexpr
    case AExpr(e) =>
      var expr :- ResolveExpr(e, rs, ls.varMap);
      return Success(AExpr(expr));
    case AAssertion(s) =>
      var stmt :- ResolveStmt(s, rs, ls.(labelMap := map[], loopLabel := None));
      return Success(AAssertion(stmt));
  }

  method ResolveStmt(stmt: Raw.Stmt, rs: ResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires rs.Valid()
    ensures result.Success? ==> stmt.WellFormed(rs.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
    ensures result.Success? ==> result.value.WellFormed()
  {
    var r: Stmt;
    match stmt {
      case VarDecl(variable, init, body) =>
        if !Raw.LegalVariableName(variable.name) {
          return Failure("illegal variable name: " + variable.name);
        }
        var typ :- ResolveType(variable.typ, rs.typeMap);
        var v := new LocalVariable(variable.name, variable.isMutable, typ);
        var i;
        if init == None {
          i := None;
        } else {
          var e :- ResolveExpr(init.value, rs, ls.varMap);
          i := Some(e);
        }
        var ls' := ls.AddVariable(variable.name, v);
        assert ls'.varMap.Keys == ls.varMap.Keys + {v.name};
        var b :- ResolveStmt(body, rs, ls');
        r := VarDecl(v, i, b);

      case Assign(lhs, rhs) =>
        if lhs !in ls.varMap {
          return Failure("undeclared variable: " + lhs);
        }
        var left := ls.varMap[lhs];
        var right :- ResolveExpr(rhs, rs, ls.varMap);
        r := Assign(left, right);

      case Block(stmts) =>
        var ss := [];
        for n := 0 to |stmts|
          invariant forall stmt <- stmts[..n] :: stmt.WellFormed(rs.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall stmt: Stmt <- ss :: stmt.WellFormed()
        {
          var s :- ResolveStmt(stmts[n], rs, ls);
          ss := ss + [s];
        }
        r := Block(ss);

      case Call(_, _) =>
        r :- ResolveCallStmt(stmt, rs, ls);

      case Check(cond) =>
        var c :- ResolveExpr(cond, rs, ls.varMap);
        r := Check(c);

      case Assume(cond) =>
        var c :- ResolveExpr(cond, rs, ls.varMap);
        r := Assume(c);

      case Assert(cond) =>
        var c :- ResolveExpr(cond, rs, ls.varMap);
        r := Assert(c);

      case AForall(name, typ, body) =>
        if !Raw.LegalVariableName(name) {
          return Failure("illegal variable name: " + name);
        }
        var t :- ResolveType(typ, rs.typeMap);
        var v := new LocalVariable(name, false, t);
        var b :- ResolveStmt(body, rs, ls.AddVariable(name, v));
        r := AForall(v, b);

      case If(cond, thn, els) =>
        var c :- ResolveExpr(cond, rs, ls.varMap);
        var th :- ResolveStmt(thn, rs, ls);
        var el :- ResolveStmt(els, rs, ls);
        var branch0 := PrependAssumption(c, th);
        var branch1 := PrependAssumption(Expr.CreateNegation(c), el);
        r := Choice([branch0, branch1]);

      case IfCase(cases) =>
        if |cases| == 0 {
          return Failure("an if-case statement must have at least 1 case");
        }
        var branches := [];
        for n := 0 to |cases|
          invariant forall cs <- cases[..n] ::
            && cs.cond.WellFormed(rs.b3, ls.varMap.Keys)
            && cs.body.WellFormed(rs.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall branch: Stmt <- branches :: branch.WellFormed()
        {
          var cond :- ResolveExpr(cases[n].cond, rs, ls.varMap);
          var body :- ResolveStmt(cases[n].body, rs, ls);
          branches := branches + [PrependAssumption(cond, body)];
        }
        r := Choice(branches);

      case Loop(invariants, body) =>
        var invs :- ResolveAExprs(invariants, rs, ls);
        var loopLabel, ls' := ls.GenerateLoopLabel();
        var b :- ResolveStmt(body, rs, ls');
        r := LabeledStmt(loopLabel, Loop(invs, b));
        assert stmt.WellFormed(rs.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?) by {
          assert forall ae <- invariants :: ae.WellFormed(rs.b3, ls.varMap.Keys);
          assert ls.varMap.Keys == ls'.varMap.Keys;
          assert ls.LabelSet() == ls'.LabelSet();
          assert ls'.loopLabel.Some?;
          assert body.WellFormed(rs.b3, ls'.varMap.Keys, ls'.LabelSet(), ls'.loopLabel.Some?);
        }

      case LabeledStmt(lbl, body) =>
        if lbl in ls.labelMap {
          return Failure("duplicate label name: " + lbl);
        }
        var l := new Label(lbl);
        var b :- ResolveStmt(body, rs, ls.AddLabel(lbl, l));
        r := LabeledStmt(l, b);

      case Exit(maybeLabel) =>
        match maybeLabel {
          case None =>
            if ls.loopLabel == None {
              return Failure("an 'exit' statement outside a loop requires a label");
            }
            r := Exit(ls.loopLabel.value);
          case Some(name) =>
            var lbl :- ls.FindLabel(name);
            r := Exit(lbl);
        }

      case Return =>
        r := Exit(ls.returnLabel);

      case Probe(expr) =>
        var e :- ResolveExpr(expr, rs, ls.varMap);
        r := Probe(e);
    }
    return Success(r);
  }

  method ResolveCallStmt(stmt: Raw.Stmt, rs: ResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires stmt.Call? && rs.Valid()
    ensures result.Success? ==> stmt.WellFormed(rs.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
    ensures result.Success? ==> result.value.WellFormed()
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

    var aa: seq<CallArgument> := [];
    for n := 0 to |args|
      invariant forall i :: 0 <= i < n ==> args[i].mode == rawProc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> args[i].arg.WellFormed(rs.b3, ls.varMap.Keys)
      invariant |aa| == n
      invariant forall i :: 0 <= i < n ==> aa[i].CorrespondingMode() == proc.Parameters[i].mode && aa[i].WellFormed()
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

  function PrependAssumption(expr: Expr, stmt: Stmt): (r: Stmt)
    requires expr.WellFormed() && stmt.WellFormed()
    ensures r.WellFormed()
  {
    if stmt.Block? then
      Block([Assume(expr)] + stmt.stmts)
    else
      Block([Assume(expr), stmt])
  }

  method ResolveExpr(expr: Raw.Expr, rs: ResolverState, varMap: map<string, Variable>) returns (result: Result<Expr, string>)
    ensures result.Success? ==> expr.WellFormed(rs.b3, varMap.Keys)
    ensures result.Success? ==> result.value.WellFormed()
  {
    var r: Expr;
    match expr {
      case BLiteral(value) =>
        r := BLiteral(value);
      case ILiteral(value) =>
        r := ILiteral(value);
      case CustomLiteral(s, typeName) =>
        var typ :- ResolveType(typeName, rs.typeMap);
        if typ == BoolType || typ == IntType {
          return Failure("custom literal is not allowed for a built-in type: " + Ast.CustomLiteralToString(s, typeName));
        }
        r := CustomLiteral(s, typ);
      case IdExpr(name) =>
        if name !in varMap {
          return Failure("undeclared variable: " + name);
        }
        r := IdExpr(varMap[name]);
      case OperatorExpr(op, args) =>
        if |args| != op.ArgumentCount() {
          return Failure("operator " + op.ToString() + " expects " + Int2String(op.ArgumentCount()) + " arguments, got " + Int2String(|args|));
        }
        var resolvedArgs :- ResolveExprList(args, rs, varMap);
        r := OperatorExpr(op, resolvedArgs);
      case FunctionCallExpr(name, args) =>
        var func := new Function(name); // TODO: This is bogus. It should instead look up the already declared function
        var resolvedArgs :- ResolveExprList(args, rs, varMap);
        r := FunctionCallExpr(func, resolvedArgs);
      case LabeledExpr(name, body) =>
        var lbl := new Label(name);
        var b :- ResolveExpr(body, rs, varMap);
        r := LabeledExpr(lbl, b);
      case LetExpr(name, typeName, rhs, body) =>
        if !Raw.LegalVariableName(name) {
          return Failure("illegal variable name: " + name);
        }
        var typ :- ResolveType(typeName, rs.typeMap);
        var letVariable := new LocalVariable(name, false, typ);
        var rRhs :- ResolveExpr(rhs, rs, varMap);
        var varMap' := varMap[name := letVariable];
        assert varMap'.Keys == varMap.Keys + {name};
        var rBody :- ResolveExpr(body, rs, varMap');
        r := LetExpr(letVariable, rRhs, rBody);
      case QuantifierExpr(univ, name, typeName, patterns, body) =>
        if !Raw.LegalVariableName(name) {
          return Failure("illegal variable name: " + name);
        }
        var typ :- ResolveType(typeName, rs.typeMap);
        var quantifiedVariable := new LocalVariable(name, false, typ);
        var varMap' := varMap[name := quantifiedVariable];
        assert varMap'.Keys == varMap.Keys + {name};
        var b :- ResolveExpr(body, rs, varMap');
        var trs :- ResolvePatterns(patterns, rs, varMap');
        r := QuantifierExpr(univ, quantifiedVariable, trs, b);
    }
    return Success(r);
  }

  method ResolveExprList(exprs: seq<Raw.Expr>, rs: ResolverState, varMap: map<string, Variable>) returns (result: Result<seq<Expr>, string>)
    ensures result.Success? ==> forall expr <- exprs :: expr.WellFormed(rs.b3, varMap.Keys)
    ensures result.Success? ==> |result.value| == |exprs|
    ensures result.Success? ==> forall expr <- result.value :: expr.WellFormed()
  {
    var resolvedExprs := [];
    for n := 0 to |exprs|
      invariant forall expr <- exprs[..n] :: expr.WellFormed(rs.b3, varMap.Keys)
      invariant |resolvedExprs| == n
      invariant forall expr: Expr <- resolvedExprs :: expr.WellFormed()
    {
      var r :- ResolveExpr(exprs[n], rs, varMap);
      resolvedExprs := resolvedExprs + [r];
    }
    return Success(resolvedExprs);
  }

  method ResolvePatterns(patterns: seq<Raw.Pattern>, rs: ResolverState, varMap: map<string, Variable>) returns (result: Result<seq<Pattern>, string>)
    ensures result.Success? ==> forall tr <- patterns :: tr.WellFormed(rs.b3, varMap.Keys)
    ensures result.Success? ==> forall tr <- result.value :: tr.WellFormed()
  {
    var resolvedPatterns := [];
    for n := 0 to |patterns|
      invariant forall tr <- patterns[..n] :: tr.WellFormed(rs.b3, varMap.Keys)
      invariant forall tr: Pattern <- resolvedPatterns :: tr.WellFormed()
    {
      var exprs :- ResolveExprList(patterns[n].exprs, rs, varMap);
      resolvedPatterns := resolvedPatterns + [Pattern(exprs)];
    }
    return Success(resolvedPatterns);
  }
}