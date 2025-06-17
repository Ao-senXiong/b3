module Printer {
  import opened Basics
  import opened Ast
  import Types

  method Program(b3: Program) {
    print "// B3 program\n";
    var types := SetToSeq(b3.types);
    for i := 0 to |types| {
      print "\n";
      TypeDecl(types[i]);
    }
    var procedures := SetToSeq(b3.procedures);
    for i := 0 to |procedures| {
      print "\n";
      Procedure(procedures[i]);
    }
  }

  method TypeDecl(ty: Types.Type) {
    print "type ", ty, "\n";
  }

  method Procedure(proc: Procedure) {
    print "procedure ", proc.name, "(";
    var params := proc.parameters;
    var sep := "";
    for i := 0 to |params| {
      var param := params[i];
      print sep;
      match param.kind {
        case InOut => print "inout ";
        case Out => print "out ";
        case _ =>
      }
      print param.name, ": ", param.typ;
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


  method Statement(stmt: Stmt, indent: nat)
    decreases stmt, 0
  {
    Indent(indent);

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
      print ");\n";

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
      StmtAsBlock(thn, indent, " else ");
      StmtAsBlock(els, indent);

    case IfCase(cases) =>
      Indent(indent);
      print "if {\n";
      for i := 0 to |cases| {
        var cs := cases[i];
        Indent(indent + IndentAmount);
        print "case ";
        Expression(cs.cond);
        print " =>\n";
        Statement(cs.body, indent + IndentAmount + IndentAmount);
      }
      print "}\n";

    case Loop(lbl, invariants, body) =>
      Indent(indent);
      Label(lbl);
      print "loop";
      if invariants == Nil {
        print " ";
      } else {
        print "\n";
        PrintAExprs(indent + IndentAmount, "invariant", invariants);
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

  method VariableDecl(v: Variable) {
    match v.kind {
      case InOut => print "inout ";
      case Out => print "out ";
      case _ =>
    }
    print v.name, ": ", v.typ;
  }

  method CallArgument(arg: CallArgument) {
    match arg
    case ArgExpr(e) => Expression(e);
    case ArgLValue(name) => print name;
  }

  method PrintAExprs(indent: nat, prefix: string, aexprs: List<AExpr>)
    decreases aexprs
  {
    var a := aexprs;
    while a != Nil
      invariant aexprs nonincreases to a
      decreases a.Length()
    {
      Indent(indent);
      print prefix;
      match a.head {
        case AExpr(e) =>
          print " ";
          Expression(e);
          print "\n";
        case AAssertion(s) =>
          print "\n";
          Statement(s, indent + IndentAmount);
      }
      a := a.tail;
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
  }
}
