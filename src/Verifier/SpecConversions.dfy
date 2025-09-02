module SpecConversions {
  import opened Basics
  import opened Ast
  import AstValid
  import StaticConsistency

  export
    provides ToCheck, ToLearn, Learn
    provides Basics, Ast, AstValid, StaticConsistency

  function ToCheck(spec: seq<AExpr>): (stmts: seq<Stmt>)
    requires AstValid.AExprSeq(spec)
    ensures AstValid.StmtSeq(stmts)
  {
    if spec == [] then
      []
    else
      var ae, rest := spec[0], ToCheck(spec[1..]);
      assert AstValid.AExpr(ae);
      match ae
      case AExpr(cond) =>
        [Check(cond)] + rest
      case AAssertion(s) =>
        var L := Learn(s);
        [Assume(L)] + rest
  }

  function ToLearn(spec: seq<AExpr>): (stmts: seq<Stmt>)
    requires AstValid.AExprSeq(spec)
    ensures AstValid.StmtSeq(stmts)
  {
    if spec == [] then
      []
    else
      var ae, rest := spec[0], ToCheck(spec[1..]);
      assert AstValid.AExpr(ae);
      match ae
      case AExpr(cond) =>
        [Assume(cond)] + rest
      case AAssertion(s) =>
        var L := Learn(s);
        [Assume(L)] + rest
  }

  function Learn(stmt: Stmt): Expr
    requires AstValid.Stmt(stmt) && !StaticConsistency.ContainsNonAssertions(stmt)
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