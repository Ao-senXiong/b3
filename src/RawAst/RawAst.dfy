module RawAst {
  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import opened Values

  // Top-level program

  datatype Program = Program(types: seq<TypeName>, procedures: seq<Procedure>)
  {
    // A raw program is well-formed when
    //    + no scope declares duplicate names
    //    + every name (of a type, procedure, function, variable) resolves to a declaration
    //    + the arity of each call (of a procedure or function) matches that of the callee
    // Well-formedness of a raw program does NOT imply things like
    //    - type correctness
    //    - no duplication of actual out-going parameters
    //    - assignments only to mutable variables
    //    - additional semantic rules
    predicate WellFormed() {
      && (forall typ <- types :: typ !in BuiltInTypes)
      && (forall i, j :: 0 <= i < j < |types| ==> types[i] != types[j])
      && (forall i, j :: 0 <= i < j < |procedures| ==> procedures[i].name != procedures[j].name)
      && (forall proc <- procedures :: proc.WellFormed(this))
    }

    method FindProcedure(name: string) returns (r: Option<Procedure>) {
      if proc :| proc in procedures && proc.name == name {
        return Some(proc);
      }
      return None;
    }
  }

  // Procedures

  datatype Procedure = Procedure(name: string, parameters: seq<Parameter>, pre: List<AExpr>, post: List<AExpr>, body: Option<Stmt>)
  {
    predicate WellFormed(b3: Program) {
      && Parameter.UniqueNames(parameters)
      && var preScope := map p <- parameters | p.mode.IsIncoming() :: p.v.name := p.v;
      && pre.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, preScope, {}))
      && var scope := map p <- parameters :: p.v.name := p.v;
      && post.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, scope, {}))
      && var localNames := set p <- parameters | p.mode.IsOutgoing() :: p.v.name;
      && (body == None || body.value.WellFormed(b3, scope, localNames, {}))
    }
  }

  type Scope = map<string, Variable>

  datatype Variable = Variable(name: string, typ: TypeName, isMutable: bool) // TODO: add auto-invariant
  {
    static predicate UniqueNames(variables: seq<Variable>) {
      forall i, j :: 0 <= i < j < |variables| ==> variables[i].name != variables[j].name
    }

    static predicate UniquelyNamed(variables: set<Variable>) {
      forall v0 <- variables, v1 <- variables :: v0.name == v1.name ==> v0 == v1
    }
  }

  datatype Parameter = Parameter(mode: ParameterMode, v: Variable)
  {
    static function ToVariables(parameters: seq<Parameter>): seq<Variable> {
      SeqMap(parameters, (p: Parameter) => p.v)
    }

    static predicate UniqueNames(parameters: seq<Parameter>): (unique: bool)
      ensures unique ==> forall i, j :: 0 <= i < j < |parameters| ==> parameters[i].v.name != parameters[j].v.name
      ensures unique ==> UniquelyNamed(set p <- parameters)
    {
      var vars := ToVariables(parameters);
      forall i, j | 0 <= i < j < |parameters|
        ensures Variable.UniqueNames(vars) ==> parameters[i].v.name != parameters[j].v.name
      {
        assert vars[i] == parameters[i].v && vars[j] == parameters[j].v;
      }
      Variable.UniqueNames(vars)
    }

    static predicate UniquelyNamed(parameters: set<Parameter>) {
      forall p0 <- parameters, p1 <- parameters :: p0.v.name == p1.v.name ==> p0 == p1
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

  const OldPrefix: string := "old$"

  function OldName(name: string): string {
    OldPrefix + name
  }

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

  predicate LegalVariableName(name: string, localNames: set<string>) {
    !("_" <= name) &&
    !(OldPrefix <= name) &&
    name !in localNames
  }

  // Statements

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
  {
    predicate ContainsAssertions() {
      match this
      case Block(_, stmts) =>
        exists s <- stmts :: s.ContainsAssertions()
      case Check(_) => true
      case Assume(_) => true
      case Assert(_) => true
      case AForall(_, _) => true
      case If(_, thn, els) =>
        thn.ContainsAssertions() || els.ContainsAssertions()
      case IfCase(cases) =>
        exists c <- cases :: c.body.ContainsAssertions()
      case Loop(_, _, body) =>
        body.ContainsAssertions()
      case _=> false
    }

    predicate ContainsNonAssertions() {
      match this
      case VarDecl(_) => true
      case Assign(_, _) => true
      case Block(_, stmts) =>
        exists s <- stmts :: s.ContainsNonAssertions()
      case Call(_, _) => true
      case If(_, thn, els) =>
        thn.ContainsNonAssertions() || els.ContainsNonAssertions()
      case IfCase(cases) =>
        exists c <- cases :: c.body.ContainsNonAssertions()
      case Loop(_, _, body) => true
      case Exit(_) => true
      case Return => true
      case Probe(_) => true
      case _ => false
    }

    predicate WellFormed(b3: Program, scope: Scope, localNames: set<string>, labels: set<string>) {
      match this
      case VarDecl(v) =>
        v.isMutable && LegalVariableName(v.name, localNames)
      case ValDecl(v, rhs) =>
        && !v.isMutable && LegalVariableName(v.name, localNames)
        && rhs.Type(b3, scope) == Some(v.typ)
      case Assign(lhs, rhs) =>
        && lhs in scope.Keys
        && var v := scope[lhs];
        && v.isMutable && rhs.Type(b3, scope) == Some(v.typ)
      case Block(lbl, stmts) =>
        lbl.IsLegalIn(labels) && WellFormedStmtSeq(stmts, b3, scope, {}, lbl.AddTo(labels))
      case Call(name, args) =>
        exists proc <- b3.procedures ::
          && name == proc.name
          && MatchingParameters(proc.parameters, args)
          && (forall i :: 0 <= i < |args| ==> args[i].WellFormed(proc.parameters[i], b3, scope))
      case Check(cond) =>
        cond.Type(b3, scope) == Some(BoolTypeName)
      case Assume(cond) =>
        cond.Type(b3, scope) == Some(BoolTypeName)
      case Assert(cond) =>
        cond.Type(b3, scope) == Some(BoolTypeName)
      case AForall(v, body) =>
        && !v.isMutable && LegalVariableName(v.name, localNames)
        && body.WellFormed(b3, scope[v.name := v], localNames, labels)
        && !body.ContainsNonAssertions()
      case If(cond, thn, els) =>
        && cond.Type(b3, scope) == Some(BoolTypeName)
        && thn.WellFormed(b3, scope, localNames, labels)
        && els.WellFormed(b3, scope, localNames, labels)
      case IfCase(cases) =>
        && |cases| != 0
        && forall i :: 0 <= i < |cases| ==> var cs := cases[i];
            && cs.cond.Type(b3, scope) == Some(BoolTypeName)
            && cs.body.WellFormed(b3, scope, localNames, labels)
      case Loop(lbl, invariants, body) =>
        && lbl.IsLegalIn(labels)
        && invariants.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, scope, labels))
        && body.WellFormed(b3, scope, localNames, lbl.AddTo(labels))
      case Exit(lbl) =>
        match lbl {
          case NamedLabel(name) => name in labels
          case AnonymousLabel => true
          case ReturnLabel => false
        }
      case Return =>
        true
      case Probe(e) =>
        e.Type(b3, scope).Some?
    }

    static predicate WellFormedStmtSeq(stmts: seq<Stmt>, b3: Program, scope: Scope, localNames: set<string>, labels: set<string>) {
      if stmts == [] then
        true
      else
        var stmt, cont := stmts[0], stmts[1..];
        && stmt.WellFormed(b3, scope, localNames, labels)
        && var (scope', localNames') :=
            match stmt
            case VarDecl(v) => (scope[stmt.v.name := stmt.v], localNames + {stmt.v.name})
            case ValDecl(v, _) => (scope[stmt.v.name := stmt.v], localNames + {stmt.v.name})
            case _ => (scope, localNames);
          WellFormedStmtSeq(cont, b3, scope', localNames', labels)
    }

    static predicate MatchingParameters(parameters: seq<Parameter>, args: seq<CallArgument>) {
      && (forall i, j :: 0 <= i < j < |args| && args[i].ArgLValue? && args[j].ArgLValue? ==> args[i].name != args[j].name)
      && |args| == |parameters|
      && forall i | 0 <= i < |parameters| && parameters[i].mode.IsOutgoing() :: args[i].ArgLValue?
    }

    predicate IsEmptyBlock() {
      Block? && lbl == AnonymousLabel && stmts == []
    }
  }

  datatype Label =
    | NamedLabel(name: string)
    | AnonymousLabel
    | ReturnLabel
  {
    predicate IsLegalIn(labels: set<string>) {
      match this
      case NamedLabel(name) => name !in labels
      case AnonymousLabel => true
      case ReturnLabel => false
    }

    function AddTo(labels: set<string>): set<string> {
      match this
      case NamedLabel(name) => labels + {name}
      case _ => labels
    }
  }

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed(b3: Program, scope: Scope, labels: set<string>) {
      match this
      case AExpr(e) =>
        e.Type(b3, scope) == Some(BoolTypeName)
      case AAssertion(s) =>
        s.WellFormed(b3, scope, {}, labels) && !s.ContainsNonAssertions()
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
    case ValDecl(_, _) =>
      true
    case Check(_) =>
      true
    case Assume(e) =>
      true
    case Assert(e) =>
      true
    case AForall(v, body) =>
      ValidAssertionStatement(body)
    case Block(_, stmts) =>
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
    case ValDecl(_, _) =>
      // this is a degenerate case, where the let binding is not used anywhere
      Expr.CreateTrue()
    case Check(_) =>
      Expr.CreateTrue()
    case Assume(e) =>
      e
    case Assert(e) =>
      e
    case AForall(v, body) =>
      Expr.CreateForall(v, Learn(body))
    case Block(_, stmts) =>
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
      match s
      case ValDecl(v, rhs) =>
        Expr.CreateLet(v, rhs, LearnSeq(tail))
      case _ =>
        assert ValidAssertionStatement(s);
        Expr.CreateAnd(Learn(s), LearnSeq(tail))
  }

  datatype CallArgument =
    | ArgExpr(e: Expr)
    | ArgLValue(mode: ParameterMode /* TODO: .mode not yet used in semantics/verifier */, name: string)
  {
    predicate WellFormed(formal: Parameter, b3: Program, scope: Scope) {
      match this
      case ArgExpr(e) =>
        formal.mode == In && e.Type(b3, scope) == Some(formal.v.typ)
      case ArgLValue(_, name) =>
        && formal.mode.IsOutgoing()
        && name in scope && var v := scope[name];
        && v.isMutable && v.typ == formal.v.typ
    }

    function Eval(vals: Valuation): Value
      requires ArgLValue? ==> name in vals
    {
      match this
      case ArgExpr(e) => e.Eval(vals)
      case ArgLValue(_, name) => vals[name]
    }
  }
  
  // Expressions

  // TODO
  datatype Expr =
    | Const(value: int)
    | IdExpr(name: string)
  {
    function Type(b3: Program, scope: Scope): Option<string>
    { Some(IntTypeName) } // TODO
    function Eval(vals: Valuation): Value // TODO: either make Option<Value> or require Type(...).Some?
    { 3 } // TODO

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