module AssignmentTargets {
  import Ast

  export
    provides Compute
    provides Ast

  function Compute(stmt: Ast.Stmt): set<Ast.Variable> {
    var (vv, cc) := StmtTargets(stmt);
    if Normal in cc then vv else {}
  }

  datatype ContinuationPoint =
    | Normal
    | Abrupt(lbl: Ast.Label)

  // Return the set of free variables that are syntactically assigned anywhere in `stmt`,
  // except in those places where control flow is syntactically impossible.
  // To accomplish the latter, the function also returns the set of possible continuation
  // points of `stmt`.
  function StmtTargets(stmt: Ast.Stmt): (set<Ast.Variable>, set<ContinuationPoint>) {
    match stmt
    case VarDecl(v, _, body) =>
      var (vv, cc) := StmtTargets(body);
      (vv - {v}, cc)
    case Assign(lhs, _) =>
      ({lhs}, {Normal})
    case Block(stmts) =>
      BlockTargets(stmts)
    case Call(_, args) =>
      (set arg <- args | arg.OutgoingArgument? :: arg.arg, {Normal})
    case Check(_) => ({}, {Normal})
    case Assume(_) => ({}, {Normal})
    case Assert(_) => ({}, {Normal})
    case AForall(_, _) => ({}, {Normal})
    case Choice(branches) =>
      ChoiceTargets(branches)
    case Loop(_, body) =>
      var (vv, cc) := StmtTargets(body);
      (vv, cc - {Normal})
    case LabeledStmt(lbl, body) =>
      var (vv, cc) := StmtTargets(body);
      if Abrupt(lbl) in cc then
        (vv, cc - {Abrupt(lbl)} + {Normal})
      else
        (vv, cc)
    case Exit(lbl) =>
      ({}, {Abrupt(lbl)})
    case Probe(_) => ({}, {Normal})
  }

  function BlockTargets(stmts: seq<Ast.Stmt>): (set<Ast.Variable>, set<ContinuationPoint>) {
    if stmts == [] then
      ({}, {Normal})
    else
      var (vv, cc) := StmtTargets(stmts[0]);
      if Normal in cc then
        var (vv', cc') := BlockTargets(stmts[1..]);
        (vv + vv', cc')
      else
        (vv, cc)
  }

  function ChoiceTargets(stmts: seq<Ast.Stmt>): (set<Ast.Variable>, set<ContinuationPoint>) {
    if stmts == [] then
      ({}, {})
    else
      var (vv, cc) := StmtTargets(stmts[0]);
      var (vv', cc') := ChoiceTargets(stmts[1..]);
      (vv + vv', cc + cc')
  }
}