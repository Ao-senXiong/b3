module Printer {
  import opened Std.Wrappers
  import opened Basics
  import opened RawAst
  import Types

  method Program(b3: Program) {
    print "// B3 program\n";
    for i := 0 to |b3.types| {
      print "\n";
      TypeDecl(b3.types[i]);
    }
    for i := 0 to |b3.procedures| {
      print "\n";
      Procedure(b3.procedures[i]);
    }
  }

  method TypeDecl(ty: Types.TypeName) {
    print "type ", ty, "\n";
  }

  method Procedure(proc: Procedure) {
    print "procedure ", proc.name, "(";
    var params := proc.parameters;
    var sep := "";
    for i := 0 to |params| {
      var param := params[i];
      print sep, ParameterMode(param.mode), param.v.name, ": ", param.v.typ;
      sep := ", ";
    }
    print ")\n";

    PrintAExprs(IndentAmount, "requires", proc.pre);
    PrintAExprs(IndentAmount, "ensures", proc.post);

    match proc.body
    case None =>
    case Some(stmt) => Statement(stmt, 0);
  }

  method Indent(indent: nat) {
    for i := 0 to indent {
      print " ";
    }
  }

  const IndentAmount := 2

  method Label(lbl: Label) {
    match lbl
    case NamedLabel(name) =>
      print name, ": ";
    case _ =>
  }


  method Statement(stmt: Stmt, indent: nat, omitInitialIndent: bool := false)
    decreases stmt, 1
  {
    if !omitInitialIndent {
      Indent(indent);
    }

    match stmt
    case VarDecl(v) =>
      print "var ";
      VariableDecl(v);
      print "\n";

    case ValDecl(v, rhs) =>
      print "val ";
      VariableDecl(v);
      print " := ";
      Expression(rhs);
      print "\n";

    case Assign(lhs, rhs) =>
      print lhs, " := ";
      Expression(rhs);
      print "\n";

    case Block(lbl, stmts) =>
      Label(lbl);
      print "{\n";
      for i := 0 to |stmts| {
        Statement(stmts[i], indent + IndentAmount);
      }
      Indent(indent);
      print "}\n";

    case Call(proc, args) =>
      print proc, "(";
      var sep := "";
      for i := 0 to |args| {
        print sep;
        CallArgument(args[i]);
        sep := ", ";
      }
      print ")\n";

    case Check(e) =>
      ExpressionStmt("check", e);

    case Assume(e) =>
      ExpressionStmt("assume", e);

    case Assert(e) =>
      ExpressionStmt("assert", e);

    case AForall(v, body) =>
      print "forall ";
      VariableDecl(v);
      print " ";
      StmtAsBlock(body, indent);

    case If(cond, thn, els) =>
      print "if ";
      Expression(cond);
      print " ";
      if els.IsEmptyBlock() {
        StmtAsBlock(thn, indent);
      } else {
        StmtAsBlock(thn, indent, " else ");
        if els.If? || els.IfCase? {
          Statement(els, indent, true);
        } else {
          StmtAsBlock(els, indent);
        }
      }

    case IfCase(cases) =>
      print "if {\n";
      for i := 0 to |cases| {
        var cs := cases[i];
        Indent(indent + IndentAmount);
        print "case ";
        Expression(cs.cond);
        print " =>\n";
        BlockAsStmts(cs.body, indent + IndentAmount + IndentAmount);
      }
      Indent(indent);
      print "}\n";

    case Loop(lbl, invariants, body) =>
      Label(lbl);
      print "loop";
      if |invariants| == 0 {
        print " ";
      } else {
        print "\n";
        PrintAExprs(indent + IndentAmount, "invariant", invariants, stmt);
        Indent(indent);
      }
      StmtAsBlock(body, indent);

    case Exit(lbl) =>
      print "exit";
      match lbl {
        case NamedLabel(name) => print " ", name;
        case AnonymousLabel =>
        case ReturnLabel => print " <return>"; // this never happens for a parsed program; ReturnLabel is only used internally
      }
      print "\n";

    case Return =>
      print "return\n";

    case Probe(e) =>
      ExpressionStmt("probe", e);
  }

  method StmtAsBlock(stmt: Stmt, indent: nat, suffix: string := "\n")
    decreases stmt
  {
    print "{\n";
    match stmt {
      case Block(None, stmts) =>
        // omit the braces of the Block itself, since we're already printing braces
        for i := 0 to |stmts| {
          Statement(stmts[i], indent + IndentAmount);
        }
      case _ =>
        Statement(stmt, indent + IndentAmount);
    }
    Indent(indent);
    print "}", suffix;
  }

  method BlockAsStmts(stmt: Stmt, indent: nat)
    decreases stmt
  {
    match stmt
    case Block(AnonynousLabel, stmts) =>
      for i := 0 to |stmts| {
        Statement(stmts[i], indent);
      }
    case _ =>
      Statement(stmt, indent);
  }

  function ParameterMode(mode: ParameterMode): string {
    match mode
    case InOut => "inout "
    case Out => "out "
    case _ => ""
  }

  method VariableDecl(v: Variable) {
    print v.name, ": ", v.typ;
  }

  method CallArgument(arg: CallArgument) {
    match arg
    case ArgExpr(e) => Expression(e);
    case ArgLValue(mode, name) => print ParameterMode(mode), name;
  }

  method PrintAExprs(indent: nat, prefix: string, aexprs: seq<AExpr>, ghost parent: Stmt := Loop(AnonymousLabel, aexprs, Return))
    requires forall ae <- aexprs :: ae.AAssertion? ==> ae.s < parent
    decreases parent, 0
  {
    for i := 0 to |aexprs| {
      Indent(indent);
      print prefix, " ";
      match aexprs[i]
      case AExpr(e) =>
        Expression(e);
        print "\n";
      case AAssertion(s) =>
        Statement(s, indent, true);
    }
  }

  method ExpressionStmt(prefix: string, e: Expr) {
    print prefix, " ";
    Expression(e);
    print "\n";
  }

  method Expression(e: Expr) {
    match e
    case Const(value) => print value;
    case IdExpr(name) => print name;
  }
}
