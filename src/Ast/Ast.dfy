module Ast {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst
  import opened Values

  type Type = Types.Type
  datatype Program = Program(types: set<Type>, procedures: set<Procedure>)
  {
    predicate WellFormed()
      reads procedures
    {
      // the built-in types are included among the resolved-AST program's types
      && Types.BuiltInTypes <= (set typ <- types :: typ.Name)
      // type declarations have distinct names
      && (forall typ0 <- types, typ1 <- types :: typ0.Name == typ1.Name ==> typ0 == typ1)
      // procedure declarations have distinct names
      && (forall proc0 <- procedures, proc1 <- procedures :: proc0.Name == proc1.Name ==> proc0 == proc1)
      // procedures are well-formed
      && (forall proc <- procedures :: proc.WellFormed())
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
      && (forall formal <- Parameters :: Raw.LegalVariableName(formal.name))
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && |Parameters| == |proc.parameters|
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].name == proc.parameters[i].name)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].mode == proc.parameters[i].mode)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
    }

    predicate WellFormed()
      reads this
    {
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && (forall pre <- Pre :: pre.WellFormed())
      && (forall post <- Post :: post.WellFormed())
      && (Body.Some? ==> Body.value.WellFormed())
      // TODO: make sure free variables of Pre/Post/Body are the expected ones
    }
  }

  trait Variable extends object {
    const name: string
    const typ: Type

    predicate IsMutable()
  }

  class LocalVariable extends Variable {
    const isMutable: bool
    constructor (name: string, isMutable: bool, typ: Type)
      ensures this.name == name
    {
      this.name, this.isMutable, this.typ := name, isMutable, typ;
    }

    predicate IsMutable() {
      isMutable
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

    predicate WellFormed() {
      oldInOut.Some? <==> mode == ParameterMode.InOut
    }

     predicate IsMutable() {
      mode != ParameterMode.In
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
  {
    predicate WellFormed() {
      match this
      case VarDecl(_, initial, body) => 
        && (initial.Some? ==> initial.value.WellFormed())
        && body.WellFormed()
      case Assign(_, rhs) => rhs.WellFormed()
      case Block(stmts) => forall stmt <- stmts :: stmt.WellFormed()
      case Call(proc, args) =>
        && |args| == |proc.Parameters|
        && (forall i :: 0 <= i < |args| ==> args[i].CorrespondingMode() == proc.Parameters[i].mode)
        && (forall arg <- args :: arg.WellFormed())
      case Check(cond) => cond.WellFormed()
      case Assume(cond) => cond.WellFormed()
      case Assert(cond) => cond.WellFormed()
      case AForall(_, body) => body.WellFormed()
      case If(cases) =>
        forall c <- cases :: c.cond.WellFormed() && c.body.WellFormed()
      case Loop(invariants, body) =>
        && (forall inv <- invariants :: inv.WellFormed())
        && body.WellFormed()
      case LabeledStmt(lbl, body) => body.WellFormed()
      case Exit(_) => true
      case Probe(e) => e.WellFormed()
    }
  }

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype CallArgument =
    | InArgument(e: Expr)
    | OutgoingArgument(isInOut: bool, arg: Variable)
  {
    function CorrespondingMode(): ParameterMode {
      match this
      case InArgument(_) => ParameterMode.In
      case OutgoingArgument(isInOut, _) => if isInOut then ParameterMode.InOut else ParameterMode.Out
    }

    predicate WellFormed() {
      match this
      case InArgument(e) => e.WellFormed()
      case OutgoingArgument(_, _) => true
    }
  }

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed() {
      match this
      case AExpr(e) => e.WellFormed()
      case AAssertion(s) => s.WellFormed()
    }
  }

  datatype Expr =
    | BConst(bvalue: bool)
    | IConst(ivalue: int)
    | IdExpr(v: Variable)
  {
    predicate HasType(typ: Type) {
      match this
      case BConst(_) => typ.IsBool()
      case IConst(_) => typ.IsInt()
      case IdExpr(v) => v.typ == typ
    }

    predicate WellFormed() {
      true // TODO
    }

    function Eval(vals: Valuation): Value // TODO: either make Option<Value> or require Type(...).Some?
    { 3 } // TODO
    static function CreateNegation(e: Expr): Expr
    { if e.BConst? then BConst(!e.bvalue) else e } // TODO
  }
}