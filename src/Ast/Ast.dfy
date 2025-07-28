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
    const Parameters: seq<Parameter>
    var Pre: seq<AExpr>
    var Post: seq<AExpr>
    var Body: Option<Stmt>

    constructor (name: string, parameters: seq<Parameter>)
      ensures Name == name && Parameters == parameters
      ensures Pre == [] && Post == [] && Body == None
    {
      Name, Parameters := name, parameters;
      Pre, Post, Body := [], [], None; // these are set after construction
    }

    ghost predicate SignatureWellFormed(proc: Raw.Procedure) {
      && Name == proc.name
      && (forall formal <- Parameters :: Raw.LegalVariableName(formal.name, {}))
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && |Parameters| == |proc.parameters|
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].name == proc.parameters[i].name)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].mode == proc.parameters[i].mode)
      && (forall i :: 0 <= i < |Parameters| ==> (Parameters[i].oldInOut.Some? <==> proc.parameters[i].mode == Raw.InOut))
    }
  }

  trait Variable extends object {
    const name: string
    const typ: Type
  }

  class LocalVariable extends Variable {
    const isMutable: bool

    constructor (name: string, isMutable: bool, typ: Type)
      ensures this.name == name
    {
      this.name, this.isMutable, this.typ := name, isMutable, typ;
    }
  }

  class Parameter extends Variable {
    const mode: ParameterMode
    const oldInOut: Option<Variable>

    constructor (name: string, mode: ParameterMode, typ: Type, oldInOut: Option<Variable>)
      ensures this.name == name && this.mode == mode && this.typ == typ && this.oldInOut == oldInOut
    {
      this.name, this.mode, this.typ := name, mode, typ;
      this.oldInOut := oldInOut;
    }
  }

  type ParameterMode = Raw.ParameterMode

  class Label {
    const name: string
    constructor (name: string)
      ensures this.name == name
    {
      this.name := name;
    }
  }

  datatype Stmt =
    | VarDecl(v: Variable, initial: Option<Expr>, body: Stmt)
    | Assign(lhs: Variable, rhs: Expr)
    | Block(stmts: seq<Stmt>)
    | Call(proc: Procedure, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(v: Variable, body: Stmt)
    // Control flow
    | If(cases: seq<Case>)
    | Loop(invariants: seq<AExpr>, body: Stmt)
    | LabeledStmt(lbl: Label, body: Stmt)
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
    | IdExpr(v: Variable)
  {
    function Type(b3: Program, scope: set<string>): Option<string>
    { Some(Types.IntTypeName) } // TODO
    function Eval(vals: Valuation): Value // TODO: either make Option<Value> or require Type(...).Some?
    { 3 } // TODO
    static function CreateNegation(e: Expr): Expr
    { if e.Const? then Const(- e.value) else e } // TODO
  }
}