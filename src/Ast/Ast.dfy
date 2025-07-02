module Ast {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst

  type Type = Types.Type
  datatype Program = Program(types: set<Type>, procedures: set<Procedure>)
  {
    predicate WellFormed() {
      && Types.BuiltInTypes <= (set typ <- types :: typ.Name)
      && (forall typ0 <- types, typ1 <- types :: typ0.Name == typ1.Name ==> typ0 == typ1)
      && (forall proc0 <- procedures, proc1 <- procedures :: proc0.Name == proc1.Name ==> proc0 == proc1)
    }
  }

  class Procedure {
    const Name: string
    const Parameters: seq<Variable>
    const Pre: List<AExpr>
    const Post: List<AExpr>
    var Body: Option<Stmt>

    constructor (name: string, parameters: seq<Variable>, pre: List<AExpr>, post: List<AExpr>)
      ensures Name == name
    {
      Name, Parameters, Pre, Post := name, parameters, pre, post;
      Body := None;
    }
  }

  datatype Variable = Variable(name: string, typ: Type, isMutable: bool) // TODO: add auto-invariant
  type Parameter = Raw.Parameter
  type ParameterMode = Raw.ParameterMode

  type Label = Raw.Label

  datatype Stmt =
    | VarDecl(v: Variable)
    | ValDecl(v: Variable, rhs: Expr)
    | Assign(lhs: string, rhs: Expr)
    | Block(lbl: Label, stmts: seq<Stmt>)
    | Call(name: string, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(v: Variable, body: Stmt)
    // Control flow
    | If(cond: Expr, thn: Stmt, els: Stmt)
    | IfCase(cases: seq<Case>)
    | Loop(lbl: Label, invariants: List<AExpr>, body: Stmt)
    | Exit(lbl: Label)
    | Return
    // Error reporting
    | Probe(e: Expr)

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype CallArgument =
    | ArgExpr(e: Expr)
    | ArgLValue(mode: ParameterMode, name: string)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)

  datatype Expr =
    | Const(value: int)
    | IdExpr(name: string)
}