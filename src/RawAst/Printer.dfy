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
      print sep, ParameterMode(param.mode), param.name, ": ", param.typ;
      sep := ", ";
    }
    print ")\n";

    PrintAExprs(IndentAmount, "requires", proc.pre);
    PrintAExprs(IndentAmount, "ensures", proc.post);

    match proc.body
    case None =>
    case Some(stmt) => StmtAsBlock(stmt, 0);
  }

  method Indent(indent: nat) {
    for i := 0 to indent {
      print " ";
    }
  }

  const IndentAmount := 2

  method Statement(stmt: Stmt, indent: nat, followedByEndCurly: bool := false, omitInitialIndent: bool := false)
    decreases stmt, 1
  {
    if !omitInitialIndent {
      Indent(indent);
    }

    match stmt
    case VarDecl(v, init, body) =>
      if followedByEndCurly {
        VariableDeclaration(v, init, body, indent, followedByEndCurly);
      } else {
        print "{\n";
        Indent(indent + IndentAmount);
        VariableDeclaration(v, init, body, indent + IndentAmount, true);
        Indent(indent);
        print "}\n";
      }

    case Assign(lhs, rhs) =>
      print lhs, " := ";
      Expression(rhs);
      print "\n";

    case Block(stmts) =>
      print "{\n";
      StatementList(stmts, indent + IndentAmount);
      Indent(indent);
      print "}\n";

    case Call(proc, args) =>
      print proc, "(";
      var sep := "";
      for i := 0 to |args| {
        print sep, ParameterMode(args[i].mode);
        Expression(args[i].arg);
        sep := ", ";
      }
      print ")\n";

    case Check(e) =>
      ExpressionStmt("check", e);

    case Assume(e) =>
      ExpressionStmt("assume", e);

    case Assert(e) =>
      ExpressionStmt("assert", e);

    case AForall(name, typ, body) =>
      print "forall ", name, ": ", typ, " ";
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
          Statement(els, indent, omitInitialIndent := true);
        } else {
          StmtAsBlock(els, indent);
        }
      }

    case IfCase(cases) =>
      print "if ";
      if |cases| == 0 {
        Indent(indent);
        print "case false {\n";
        Indent(indent);
        print "}\n";
      } else {
        for i := 0 to |cases| {
          var cs := cases[i];
          print "case ";
          Expression(cs.cond);
          print " ";
          StmtAsBlock(cs.body, indent, if i == |cases| - 1 then "\n" else " ");
        }
      }

    case Loop(invariants, body) =>
      print "loop";
      if |invariants| == 0 {
        print " ";
      } else {
        print "\n";
        PrintAExprs(indent + IndentAmount, "invariant", invariants, stmt);
        Indent(indent);
      }
      StmtAsBlock(body, indent);

    case LabeledStmt(lbl, body) =>
      print lbl, ": ";
      if body.Loop? {
        Statement(body, indent, omitInitialIndent := true);
      } else {
        StmtAsBlock(body, indent);
      }

    case Exit(lbl) =>
      print "exit";
      if lbl.Some? {
        print " ", lbl.value;
      }
      print "\n";

    case Return =>
      print "return\n";

    case Probe(e) =>
      ExpressionStmt("probe", e);
  }

  method VariableDeclaration(v: Variable, init: Option<Expr>, body: Stmt, indent: nat, followedByEndCurly: bool)
    decreases body, 3
  {
    print if v.isMutable then "var " else "val ";
    print v.name, ": ", v.typ;
    match init {
      case None =>
      case Some(e) =>
        print " := ";
        Expression(e);
    }
    print "\n";
    BlockAsStatementList(body, indent, followedByEndCurly);
  }

  method StmtAsBlock(stmt: Stmt, indent: nat, suffix: string := "\n")
    decreases stmt
  {
    print "{\n"; // always omits initial indent
    match stmt {
      case Block(stmts) =>
        // omit the braces of the Block itself, since we're already printing braces
        StatementList(stmts, indent + IndentAmount);
      case _ =>
        Statement(stmt, indent + IndentAmount);
    }
    Indent(indent);
    print "}", suffix;
  }

  method BlockAsStatementList(stmt: Stmt, indent: nat, followedByEndCurly: bool)
    decreases stmt, 2
  {
    match stmt
    case Block(stmts) =>
      StatementList(stmts, indent);
    case _ =>
      Statement(stmt, indent, followedByEndCurly);
  }

  method StatementList(stmts: seq<Stmt>, indent: nat, followedByEndCurly: bool := true) {
    for i := 0 to |stmts| {
      Statement(stmts[i], indent, followedByEndCurly && i == |stmts| - 1);
    }
  }

  function ParameterMode(mode: ParameterMode): string {
    match mode
    case InOut => "inout "
    case Out => "out "
    case _ => ""
  }

  method PrintAExprs(indent: nat, prefix: string, aexprs: seq<AExpr>, ghost parent: Stmt := Loop(aexprs, Return))
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
        Statement(s, indent, omitInitialIndent := true);
    }
  }

  method ExpressionStmt(prefix: string, e: Expr) {
    print prefix, " ";
    Expression(e);
    print "\n";
  }

  method Expression(e: Expr) {
    match e
    case BConst(value) => print value;
    case IConst(value) => print value;
    case IdExpr(name) => print name;
  }
}
