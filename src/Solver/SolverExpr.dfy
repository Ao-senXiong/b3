module SolverExpr {
  import Std.Collections.Seq
  import opened Basics

  export
    reveals SVar, SVar.name
    reveals SExprPrintConfig
    provides SExpr, SExpr.ToString
    provides SExpr.Boolean, SExpr.Integer, SExpr.Id, SExpr.Eq, SExpr.Negation, SExpr.BigAnd

  class SVar {
    const name: string
    constructor (name: string) {
      this.name := name;
    }
  }

  datatype SExprPrintConfig = SExprPrintConfig(newlines: bool, indent: string)
  {
    function ExtraIdent(n: nat): SExprPrintConfig {
      if !newlines then this
      else this.(indent := indent + seq(n, i => ' '))
    }
    function Space(): string {
      if newlines then "\n" + indent
      else " "
    }
  }

  datatype SExpr // pun: solver expression
    =
    | S(string) // Single name
    | PP(seq<SExpr>) // Parentheses
  {
    opaque function ToString(config: SExprPrintConfig := SExprPrintConfig(false, "")): string {
      match this {
        case S(name) => if name == "" then "()" else name
        case PP(s) =>
          if |s| > 0 then
            var name := s[0].ToString(config);
            var newIndent := config.ExtraIdent(2);
            "(" + name +
            Basics.SeqToString(s[1..], (argument: SExpr) requires argument < this =>
                                 newIndent.Space() + argument.ToString(newIndent)
            ) + ")"
          else
            "()"
      }
    }
    // SExpr builders

    static const TRUE := "true"
    static const FALSE := "false"
    static const EQ := "="
    static const NOT := "not"
    static const AND := "and"

    static function Boolean(b: bool): SExpr {
      S(if b then TRUE else FALSE)
    }
    static function Integer(x: int): SExpr {
      S(Int2String(x))
    }
    static function Id(x: SVar): SExpr {
      S(x.name)
    }
    static function Eq(e0: SExpr, e1: SExpr): SExpr {
      PP([S(EQ), e0, e1])
    }
    static function Negation(e: SExpr): SExpr {
      PP([S(NOT), e])
    }
    static function BigAnd(ee: seq<SExpr>): SExpr {
      if |ee| == 0 then
        Boolean(true)
      else if |ee| == 1 then
        ee[0]
      else
        PP([S(AND)] + ee)
    }
  }
}