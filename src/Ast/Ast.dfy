module Ast {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst
  import opened Values

  type Type = Types.Type
  datatype Program = Program(types: set<Type>, procedures: set<Procedure>)
  {
    predicate WellFormed() {
      // the built-in types are included among the resolved-AST program's types
      && Types.BuiltInTypes <= (set typ <- types :: typ.Name)
      // type declarations have distinct names
      && (forall typ0 <- types, typ1 <- types :: typ0.Name == typ1.Name ==> typ0 == typ1)
      // procedure declarations have distinct names
      && (forall proc0 <- procedures, proc1 <- procedures :: proc0.Name == proc1.Name ==> proc0 == proc1)
    }
  }

  class Procedure {
    const Name: string
    const Parameters: seq<Variable>
    const Pre: seq<AExpr>
    const Post: seq<AExpr>
    var Body: Option<Stmt>

    constructor (name: string, parameters: seq<Variable>, pre: seq<AExpr>, post: seq<AExpr>)
      ensures Name == name && Body == None
    {
      Name, Parameters, Pre, Post := name, parameters, pre, post;
      Body := None; // for a procedure with a body, .Body will be updated later
    }
  }

  class Variable {
    const name: string
    const isMutable: bool
    const typ: Type

    constructor Variable(name: string, isMutable: bool, typ: Type)
      ensures this.name == name
    {
      this.name, this.isMutable, this.typ := name, isMutable, typ;
    }
  }

  type Parameter = Raw.Parameter
  type ParameterMode = Raw.ParameterMode

  datatype Label =
    | NamedLabel(name: string)
    | ReturnLabel
  {
    predicate IsLegalIn(labels: set<string>) {
      match this
      case NamedLabel(name) => name !in labels
      case ReturnLabel => false
    }

    function AddTo(labels: set<string>): set<string> {
      match this
      case NamedLabel(name) => labels + {name}
      case _ => labels
    }
  }

  datatype Stmt =
    | VarDecl(v: Variable, initial: Option<Expr>, body: Stmt)
    | Assign(lhs: string, rhs: Expr)
    | Block(stmts: seq<Stmt>)
    | Call(name: string, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(v: Variable, body: Stmt)
    // Control flow
    | If(cond: Expr, thn: Stmt, els: Stmt)
    | IfCase(cases: seq<Case>)
    | Loop(invariants: List<AExpr>, body: Stmt)
    | Exit(lbl: Label)
    // Error reporting
    | Probe(e: Expr)

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype CallArgument =
    | InArgument(e: Expr)
    | OutgoingArgument(isInOut: bool, arg: Variable)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    /*
    function Eval(vals: Valuation): Value
      requires ArgLValue? ==> name in vals
    {
      match this
      case ArgExpr(e) => e.Eval(vals)
      case ArgLValue(_, name) => vals[name]
    }
    */
  }

  datatype Expr =
    | Const(value: int)
    | IdExpr(name: string)
  {
    function Type(b3: Program, scope: set<string>): Option<string>
    { Some(Types.IntTypeName) } // TODO
    function Eval(vals: Valuation): Value // TODO: either make Option<Value> or require Type(...).Some?
    { 3 } // TODO
  }
}