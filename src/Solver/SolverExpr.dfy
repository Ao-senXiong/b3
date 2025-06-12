module SolverExpr {
  export
    reveals Var, Var.name
    provides SExpr
    provides CreateTrue, CreateIdExpr, CreateEq, CreateNegation, CreateBigAnd

  class Var {
    const name: string
    constructor (name: string) {
      this.name := name;
    }
  }

  type SExpr // pun: solver expression
    = string // TODO

  function CreateTrue(): SExpr
  { "TRUE" } // TODO
  function CreateIdExpr(x: Var): SExpr
  { x.name } // TODO
  function CreateEq(e0: SExpr, e1: SExpr): SExpr
  { "(EQ " + e0 + " " + e1 + ")" } // TODO
  function CreateNegation(e: SExpr): SExpr
  { "(NOT " + e + ")" } // TODO
  function CreateBigAnd(ee: seq<SExpr>): SExpr
  {  // TODO
    if |ee| == 0 then
      CreateTrue()
    else if |ee| == 1 then
      ee[0]
    else
       "(AND" + ToList(ee) + ")"
  }
  function ToList(ee: seq<SExpr>): SExpr
  { if |ee| == 0 then "" else " " + ee[0] + ToList(ee[1..]) }
}