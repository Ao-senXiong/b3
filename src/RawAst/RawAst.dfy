module RawAst {
  import opened Std.Wrappers
  import opened Basics
  import opened Types

  // Top-level program

  // A raw program reflects program that has been parsed.
  datatype Program = Program(types: seq<TypeName>, procedures: seq<Procedure>)
  {
    // A raw program is well-formed when its identifiers resolve to declarations and some basic
    // properties hold:
    //    + no scope declares duplicate names
    //    + every name (of a type, procedure, function, variable) resolves to a declaration
    //    + the arity of each call (of a procedure or function) matches that of the callee
    //    + parameter modes of formal and actual call arguments match
    // Well-formedness of a raw program does NOT imply things like
    //    - type correctness
    //    - no duplication of actual out-going parameters
    //    - assignments only to mutable variables
    //    - additional semantic rules
    predicate WellFormed() {
      // user-defined types do not use the names of built-in types
      && (forall typ <- types :: typ !in BuiltInTypes)
      // user-defined types have distinct names
      && (forall i, j :: 0 <= i < j < |types| ==> types[i] != types[j])
      // procedures have distinct names
      && (forall i, j :: 0 <= i < j < |procedures| ==> procedures[i].name != procedures[j].name)
      // procedure declarations are well-formed
      && (forall proc <- procedures :: proc.WellFormed(this))
    }

    method FindProcedure(name: string) returns (r: Option<Procedure>) {
      if proc :| proc in procedures && proc.name == name {
        return Some(proc);
      }
      return None;
    }

    predicate IsType(typ: TypeName) {
      typ in BuiltInTypes || typ in types
    }
  }

  // Procedures

  datatype Procedure = Procedure(name: string, parameters: seq<Parameter>, pre: seq<AExpr>, post: seq<AExpr>, body: Option<Stmt>)
  {
    predicate WellFormed(b3: Program) {
      // parameters have legal names and valid types
      && (forall p <- parameters :: LegalVariableName(p.name, {}) && b3.IsType(p.typ))
      // formal parameters have distinct names
      && Parameter.UniqueNames(parameters)
      // set up the scopes: precondition, postcondition, body
      && var preScope := set p <- parameters | p.mode.IsIncoming() :: p.name;
      && var bodyScope := set p <- parameters :: p.name;
      && var postScope := bodyScope + (set p <- parameters | p.mode == InOut :: OldName(p.name));
      // pre- and postconditions are well-formed
      && (forall ae <- pre :: ae.WellFormed(b3, preScope))
      && (forall ae <- post :: ae.WellFormed(b3, postScope))
      // body, if any, is well-formed
      && (body == None || body.value.WellFormed(b3, bodyScope, {}, false))
    }
  }

  type Scope = set<string>

  datatype Variable = Variable(name: string, isMutable: bool, typ: TypeName) // TODO: add auto-invariant
  {
    static predicate UniqueNames(variables: seq<Variable>) {
      forall i, j :: 0 <= i < j < |variables| ==> variables[i].name != variables[j].name
    }

    static predicate UniquelyNamed(variables: set<Variable>) {
      forall v0 <- variables, v1 <- variables :: v0.name == v1.name ==> v0 == v1
    }
  }

  datatype Parameter = Parameter(name: string, mode: ParameterMode, typ: TypeName)
  {
    static predicate UniqueNames(parameters: seq<Parameter>) {
      && (forall i, j :: 0 <= i < j < |parameters| ==> parameters[i].name != parameters[j].name)
    }

    static predicate UniquelyNamed(parameters: set<Parameter>) {
      forall p0 <- parameters, p1 <- parameters :: p0.name == p1.name ==> p0 == p1
    }
  }

  datatype ParameterMode = In | InOut | Out
  {
    predicate IsIncoming() {
      this in {In, InOut}
    }
    predicate IsOutgoing() {
      this in {InOut, Out}
    }
  }

  /*
  lemma UniqueNamesImpliesUniqueOldNames(parameters: set<Parameter>)
    requires Parameter.UniquelyNamed(parameters)
    ensures forall p0 <- parameters, p1 <- parameters :: OldName(p0.v.name) == OldName(p1.v.name) ==> p0 == p1
  {
    forall p0 <- parameters, p1 <- parameters | OldName(p0.v.name) == OldName(p1.v.name)
      ensures p0 == p1
    {
      assert p0.v.name == OldName(p0.v.name)[|OldPrefix|..];
      assert p1.v.name == OldName(p1.v.name)[|OldPrefix|..];
    }
  }
  */

  const OldPrefix: string := "old$"

  function OldName(name: string): string {
    OldPrefix + name
  }

  predicate LegalVariableName(name: string, scope: Scope) {
    !("_" <= name) &&
    !(OldPrefix <= name) &&
    name !in scope
  }

  // Statements

  datatype Stmt =
    | VarDecl(v: Variable, init: Option<Expr>, body: Stmt)
    | Assign(lhs: string, rhs: Expr)
    | Block(stmts: seq<Stmt>)
    | Call(name: string, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(name: string, typ: TypeName, body: Stmt)
    // Control flow
    | If(cond: Expr, thn: Stmt, els: Stmt)
    | IfCase(cases: seq<Case>)
    | Loop(invariants: seq<AExpr>, body: Stmt)
    | LabeledStmt(lbl: string, stmt: Stmt)
    | Exit(maybeLabel: Option<string>)
    | Return
    // Error reporting
    | Probe(e: Expr)
  {
    predicate ContainsAssertions() {
      match this
      case VarDecl(_, _, body) =>
        body.ContainsAssertions()
      case Block(stmts) =>
        exists s <- stmts :: s.ContainsAssertions()
      case Check(_) => true
      case Assume(_) => true
      case Assert(_) => true
      case AForall(_, _, _) => true
      case If(_, thn, els) =>
        thn.ContainsAssertions() || els.ContainsAssertions()
      case IfCase(cases) =>
        exists c <- cases :: c.body.ContainsAssertions()
      case Loop(_, body) =>
        body.ContainsAssertions()
      case LabeledStmt(_, body) =>
        body.ContainsAssertions()
      case _=> false
    }

    predicate ContainsNonAssertions() {
      match this
      case VarDecl(_, _, body) =>
        body.ContainsNonAssertions()
      case Assign(_, _) => true
      case Block(stmts) =>
        exists s <- stmts :: s.ContainsNonAssertions()
      case Call(_, _) => true
      case If(_, thn, els) =>
        thn.ContainsNonAssertions() || els.ContainsNonAssertions()
      case IfCase(cases) =>
        exists c <- cases :: c.body.ContainsNonAssertions()
      case Loop(_, _) => true // loops are not allowed in assertions
      case LabeledStmt(_, _) => true // assertions are not allowed to be labeled
      case Exit(_) => true
      case Return => true
      case Probe(_) => true
      case _ => false
    }

    predicate WellFormed(b3: Program, scope: Scope, labels: set<string>, insideLoop: bool) {
      match this
      case VarDecl(v, init, body) =>
        && LegalVariableName(v.name, scope)
        && b3.IsType(v.typ)
        && (init.Some? ==> init.value.WellFormed(b3, scope))
        && body.WellFormed(b3, scope + {v.name}, labels, insideLoop)
      case Assign(lhs, rhs) =>
        && lhs in scope
        && rhs.WellFormed(b3, scope)
      case Block(stmts) =>
        forall stmt <- stmts :: stmt.WellFormed(b3, scope, labels, insideLoop)
      case Call(name, args) =>
        // the call goes to a procedure in the program
        exists proc <- b3.procedures | name == proc.name ::
          // the number of arguments agrees with the number of formal parameters
          && |args| == |proc.parameters|
          // the parameter modes match
          && (forall i :: 0 <= i < |proc.parameters| ==> args[i].mode == proc.parameters[i].mode)
          // the arguments are well-formed
          && (forall i :: 0 <= i < |args| ==> args[i].arg.WellFormed(b3, scope))
      case Check(cond) =>
        cond.WellFormed(b3, scope)
      case Assume(cond) =>
        cond.WellFormed(b3, scope)
      case Assert(cond) =>
        cond.WellFormed(b3, scope)
      case AForall(name, typ, body) =>
        && LegalVariableName(name, scope)
        && b3.IsType(typ)
        && body.WellFormed(b3, scope + {name}, labels, insideLoop)
        && !body.ContainsNonAssertions()
      case If(cond, thn, els) =>
        && cond.WellFormed(b3, scope)
        && thn.WellFormed(b3, scope, labels, insideLoop)
        && els.WellFormed(b3, scope, labels, insideLoop)
      case IfCase(cases) =>
        && |cases| != 0
        && forall cs <- cases ::
            && cs.cond.WellFormed(b3, scope)
            && cs.body.WellFormed(b3, scope, labels, insideLoop)
      case Loop(invariants, body) =>
        && (forall ae <- invariants :: ae.WellFormed(b3, scope))
        && body.WellFormed(b3, scope, labels, true)
      case LabeledStmt(lbl, body) =>
        && lbl !in labels
        && body.WellFormed(b3, scope, labels + {lbl}, insideLoop)
      case Exit(optionalLabel) =>
        match optionalLabel {
          case Some(lbl) => lbl in labels
          case None => insideLoop
        }
      case Return =>
        true
      case Probe(e) =>
        e.WellFormed(b3, scope)
    }

    predicate IsEmptyBlock() {
      Block? && |stmts| == 0
    }
  }

  datatype CallArgument = CallArgument(mode: ParameterMode, arg: Expr)

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed(b3: Program, scope: Scope) {
      match this
      case AExpr(e) =>
        e.WellFormed(b3, scope)
      case AAssertion(s) =>
        s.WellFormed(b3, scope, {}, false) && !s.ContainsNonAssertions()
    }

    ghost predicate Valid() {
      AAssertion? ==> ValidAssertionStatement(s)
    }

    function ToCheckStmt(): Stmt {
      match this
      case AExpr(e) => Assert(e)
      case AAssertion(s) => s
    }

    function ToAssumeStmt(): Stmt
      requires Valid()
    {
      match this
      case AExpr(e) => Assume(e)
      case AAssertion(s) => Assume(Learn(s))
    }
  }

  // ValidAssertionStatement(s) is a deep version of !s.ContainsNonAssertions()
  ghost predicate ValidAssertionStatement(s: Stmt) {
    match s
    case VarDecl(v, init, body) =>
      !v.isMutable && init.Some? && ValidAssertionStatement(body)
    case Check(_) =>
      true
    case Assume(e) =>
      true
    case Assert(e) =>
      true
    case AForall(_, _, body) =>
      ValidAssertionStatement(body)
    case Block(stmts) =>
      forall s <- stmts :: ValidAssertionStatement(s)
    case If(cond, thn, els) =>
      ValidAssertionStatement(thn) && ValidAssertionStatement(els)
    case IfCase(cases) =>
      forall c <- cases :: ValidAssertionStatement(c.body)
    case _ =>
      false
  }

  function Learn(s: Stmt): Expr
    requires ValidAssertionStatement(s)
  {
    match s
    case VarDecl(v, Some(rhs), body) =>
      Expr.CreateLet(v, rhs, Learn(body))
    case Check(_) =>
      Expr.CreateTrue()
    case Assume(e) =>
      e
    case Assert(e) =>
      e
    case AForall(name, typ, body) =>
      Expr.CreateForall(Variable(name, false, typ), Learn(body))
    case Block(stmts) =>
      LearnSeq(stmts)
    case If(cond, thn, els) =>
      Expr.CreateAnd(
        Expr.CreateImplies(cond, Learn(thn)),
        Expr.CreateImplies(Expr.CreateNegation(cond), Learn(els))
      )
    case IfCase(cases) =>
     Expr.CreateBigOr(SeqMap(cases, (c: Case) requires c in cases => Expr.CreateAnd(c.cond, Learn(c.body))))
  }

  function LearnSeq(stmts: seq<Stmt>): Expr
    requires forall s <- stmts :: ValidAssertionStatement(s)
  {
    if stmts == [] then
      Expr.CreateTrue()
    else
      var s, tail := stmts[0], stmts[1..];
      assert ValidAssertionStatement(s);
      Expr.CreateAnd(Learn(s), LearnSeq(tail))
  }

  // Expressions

  // TODO
  datatype Expr =
    | Const(value: int)
    | IdExpr(name: string)
  {
    predicate WellFormed(b3: Program, scope: Scope)
    { true } // TODO

    static function CreateTrue(): Expr
    { Const(10) } // TODO
    static function CreateFalse(): Expr
    { Const(-10) } // TODO
    static function CreateNegation(e: Expr): Expr
    { if e.Const? then Const(- e.value) else e } // TODO
    static function CreateAnd(e0: Expr, e1: Expr): Expr
    { if e0.Const? && e1.Const? then Const(e0.value * e1.value) else e0 } // TODO
    static function CreateBigAnd(ee: seq<Expr>): Expr {
      if |ee| == 0 then CreateTrue() else CreateAnd(ee[0], CreateBigAnd(ee[1..]))
    }
    static function CreateOr(e0: Expr, e1: Expr): Expr
    { if e0.Const? && e1.Const? then Const(e0.value + e1.value) else e0 } // TODO
    static function CreateBigOr(ee: seq<Expr>): Expr {
      if |ee| == 0 then CreateFalse() else CreateOr(ee[0], CreateBigOr(ee[1..]))
    }
    static function CreateImplies(e0: Expr, e1: Expr): Expr
    { if e0.Const? && e1.Const? then Const(-e0.value + e1.value) else e0 } // TODO
    static function CreateLet(v: Variable, rhs: Expr, body: Expr): Expr
    { if body.Const? then Const(100 * body.value) else body } // TODO
    static function CreateForall(v: Variable, body: Expr): Expr
    { if body.Const? then Const(1000 * body.value) else body } // TODO
  }
}