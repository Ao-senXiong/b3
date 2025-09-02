module AstValid {
  import Ast
  import StaticConsistency

  export
    reveals Program, Procedure, StmtSeq, Stmt, AExprSeq, AExpr
    provides Ast, StaticConsistency

  predicate Program(b3: Ast.Program)
    reads b3.procedures, b3.functions
  {
    b3.WellFormed() && StaticConsistency.Consistent(b3)
  }

  predicate Procedure(proc: Ast.Procedure)
    reads proc
  {
    proc.WellFormed() && StaticConsistency.ConsistentProc(proc)
  }

  predicate StmtSeq(stmts: seq<Ast.Stmt>) {
    forall stmt <- stmts :: Stmt(stmt)
  }

  predicate Stmt(stmt: Ast.Stmt) {
    stmt.WellFormed() && StaticConsistency.ConsistentStmt(stmt)
  }

  predicate AExprSeq(aexprs: seq<Ast.AExpr>) {
    forall ae <- aexprs :: AExpr(ae)
  }

  predicate AExpr(ae: Ast.AExpr) {
    ae.WellFormed() && StaticConsistency.ConsistentAExpr(ae)
  }
}