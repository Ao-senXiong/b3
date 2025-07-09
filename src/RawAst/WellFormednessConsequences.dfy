module WellFormednessConsequences {
/******************************
  export
    provides Stmt
    provides AboutBlock, AboutBlockStmts, AboutIf, AboutIfCase, AboutLoop, AboutAForall
    reveals StmtList, StmtSeq
    provides RawAst, Basics

  import opened Basics
  import opened RawAst

  ghost predicate Stmt(stmt: Stmt, b3: Program) {
    && b3.WellFormed()
    && exists scope, localNames, labels :: stmt.WellFormed(b3, scope, localNames, labels)
  }

  ghost predicate StmtList(stmts: List<Stmt>, b3: Program) {
    match stmts
    case Nil => true
    case Cons(s, tail) => Stmt(s, b3) && StmtList(tail, b3)
  }

  ghost predicate StmtSeq(stmts: seq<Stmt>, b3: Program) {
    forall s <- stmts :: Stmt(s, b3)
  }

  lemma AboutBlock(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && stmt.Block?
    ensures StmtSeq(stmt.stmts, b3)
  {
    var scope, localNames, labels :| stmt.WellFormed(b3, scope, localNames, labels);
    localNames, labels := {}, stmt.lbl.AddTo(labels);
    for i := 0 to |stmt.stmts|
      invariant RawAst.Stmt.WellFormedStmtSeq(stmt.stmts[i..], b3, scope, localNames, labels)
      invariant forall s <- stmt.stmts[..i] :: Stmt(s, b3)
    {
      var ss := stmt.stmts[i..];
      var s := ss[0];
      assert s.WellFormed(b3, scope, localNames, labels);
      if s.VarDecl? || s.ValDecl? {
        scope, localNames := scope[s.v.name := s.v], localNames + {s.v.name};
      }
    }

  }

  lemma AboutBlockStmts(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && stmt.Block?
    ensures StmtSeq(stmt.stmts + [Exit(stmt.lbl)], b3)
  {
    assert StmtSeq(stmt.stmts, b3) by {
      AboutBlock(stmt, b3);
    }

    var exit := Exit(stmt.lbl);
    assert Stmt(exit, b3) by {
      assert exit.WellFormed(b3, map[], {}, stmt.lbl.AddTo({}));
    }    
  }

  lemma AboutIf(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && stmt.If?
    ensures Stmt(stmt.thn, b3) && Stmt(stmt.els, b3)
  {
    var scope, localNames, labels :| stmt.WellFormed(b3, scope, localNames, labels);
    assert stmt.thn.WellFormed(b3, scope, localNames, labels);
    assert stmt.els.WellFormed(b3, scope, localNames, labels);
  }

  lemma AboutIfCase(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && stmt.IfCase?
    ensures forall cs <- stmt.cases :: Stmt(cs.body, b3)
  {
    var scope, localNames, labels :| stmt.WellFormed(b3, scope, localNames, labels);
    assert forall i :: 0 <= i < |stmt.cases| ==> var cs := stmt.cases[i]; cs.body.WellFormed(b3, scope, localNames, labels);
  }

  lemma AboutLoop(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && stmt.Loop?
    ensures Stmt(stmt.body, b3)
  {
    var scope, localNames, labels :| stmt.WellFormed(b3, scope, localNames, labels);
    assert stmt.body.WellFormed(b3, scope, localNames, stmt.lbl.AddTo(labels));
  }

  lemma AboutAForall(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && stmt.AForall?
    ensures ValidAssertionStatement(stmt) && Stmt(stmt.body, b3)
  {
    WellFormedAForallImpliesValidAssertionStatement(stmt, b3);
    var scope, localNames, labels :| stmt.WellFormed(b3, scope, localNames, labels);
    var AForall(v, body) := stmt;
    assert body.WellFormed(b3, scope[v.name := v], localNames, labels);
  }

  lemma WellFormedAForallImpliesValidAssertionStatement(stmt: Stmt, b3: Program)
    requires Stmt(stmt, b3) && !stmt.ContainsNonAssertions()
    ensures ValidAssertionStatement(stmt)
  {
    match stmt
    case ValDecl(_, _) =>
    case Check(_) =>
    case Assume(_) =>
    case Assert(_) =>
    case Block(_, stmts) =>
      AboutBlock(stmt, b3);
    case If(_, thn, els) =>
      AboutIf(stmt, b3);
    case IfCase(cases) =>
      AboutIfCase(stmt, b3);
    case AForall(v, body) =>
      var scope, localNames, labels :| stmt.WellFormed(b3, scope, localNames, labels);
      assert !body.ContainsNonAssertions();
      assert ValidAssertionStatement(body) by {
        assert body.WellFormed(b3, scope[v.name := v], localNames, labels);
        WellFormedAForallImpliesValidAssertionStatement(body, b3);
      }
  }
  */
******************************/
}