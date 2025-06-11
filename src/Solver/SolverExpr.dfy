module SolverExpr {
  export
    reveals Var, Var.name
    provides SExpr
    provides CreateIdExpr, CreateEq, CreateNegation, CreateBigAnd

  class Var {
    const name: string
    constructor (name: string) {
      this.name := name;
    }
  }

  type SExpr // pun: solver expression

  function CreateIdExpr(x: Var): SExpr
  function CreateEq(e0: SExpr, e1: SExpr): SExpr
  function CreateNegation(e: SExpr): SExpr
  function CreateBigAnd(ee: seq<SExpr>): SExpr
}