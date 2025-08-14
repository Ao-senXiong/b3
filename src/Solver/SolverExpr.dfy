module SolverExpr {
  import opened Std.Wrappers
  import Std.Collections.Seq
  import opened Basics

  export
    reveals SDeclaration, SDeclaration.name
    reveals SType
    provides SType.SplitInputsOutput, SType.TypesToSExpr, SType.ToSExpr
    reveals STypedDeclaration, STypedDeclaration.typ
    reveals SVar
    reveals SExprPrintConfig
    provides SExpr, SExpr.ToString
    provides SExpr.Boolean, SExpr.Integer, SExpr.Id, SExpr.FuncAppl, SExpr.Eq, SExpr.Negation, SExpr.BigAnd
    provides Wrappers

  trait SDeclaration extends object {
    const name: string
  }

  class STypeDecl extends SDeclaration {
    constructor (name: string) {
      this.name := name;
    }
  }

  datatype SType =
    | SBool
    | SInt
    | SArrow(inputs: seq<SType>, output: SType)
  {
    function SplitInputsOutput(): (seq<SType>, SType) {
      match this
      case SArrow(inputs, output) => (inputs, output)
      case _ => ([], this)
    }

    static function TypesToSExpr(types: seq<SType>, ghost parent: SType := SArrow(types, SBool)): SExpr
      requires forall typ <- types :: typ < parent
      decreases parent, 0
    {
      PP(SeqMap(types, (typ: SType) requires typ < parent => typ.ToSExpr()))
    }

    function ToSExpr(): SExpr {
      match this
      case SBool => S("Bool")
      case SInt => S("Int")
      case SArrow(inputs, output) =>
        // Actually, we don't expect this ever to happen, because SMTLib does not support types like this
        var ins := TypesToSExpr(inputs, this);
        PP([ins, output.ToSExpr()])
    }
  }

  trait STypedDeclaration extends SDeclaration {
    const typ: SType
  }

  class SVar extends STypedDeclaration {
    constructor (name: string, typ: SType) {
      this.name := name;
      this.typ := typ;
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

  datatype SExpr = // pun: solver expression
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
    static function FuncAppl(op: string, args: seq<SExpr>): SExpr {
      PP([S(op)] + args)
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