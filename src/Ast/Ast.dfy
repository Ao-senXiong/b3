module Ast {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst

  type Type = Types.Type
  datatype Program = Program(types: set<Type>, procedures: set<Procedure>)

  datatype Procedure = Procedure(name: string, parameters: seq<Variable>, pre: List<AExpr>, post: List<AExpr>, body: Option<Stmt>)

  datatype Variable = Variable(name: string, typ: Type, kind: VariableKind) // TODO: add auto-invariant
  type VariableKind = Raw.VariableKind

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
    | ArgLValue(kind: VariableKind /* TODO: .kind not yet used in semantics/verifier */, name: string)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)

  datatype Expr =
    | Const(value: int)
    | IdExpr(name: string)
}