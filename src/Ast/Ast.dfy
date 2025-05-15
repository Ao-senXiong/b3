module Ast {
  import opened Basics
  import opened Types
  import opened Values

  // Top-level program

  datatype Program = Program(types: set<Type>, procedures: set<Procedure>)
  {
    predicate WellFormed() {
      && (forall typ <- types :: typ !in BuiltInTypes)
      && (forall proc <- procedures, proc' <- procedures :: proc.name == proc'.name ==> proc == proc')
      && forall proc <- procedures :: proc.WellFormed(this)
    }
  }

  // Procedures

  datatype Procedure = Procedure(name: string, parameters: seq<Variable>, pre: List<AExpr>, post: List<AExpr>, body: Option<Stmt>)
  {
    predicate WellFormed(b3: Program) {
      && (forall p <- parameters :: p.kind.IsParameter())
      && Variable.UniqueNames(parameters)
      && var preScope := map p <- parameters | p.kind.IsIncomingParameter() :: p.name := p;
      && pre.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, preScope, {}))
      && var scope := map p <- parameters :: p.name := p;
      && post.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, scope, {}))
      && var localNames := set p <- parameters | p.kind.IsOutgoingParameter() :: p.name;
      && (body == None || body.value.WellFormed(b3, scope, localNames, {}))
    }
  }

  type Scope = map<string, Variable>

  datatype Variable = Variable(name: string, typ: Type, kind: VariableKind) // TODO: add auto-invariant
  {
    static predicate UniqueNames(variables: seq<Variable>) {
      forall i, j :: 0 <= i < j < |variables| ==> variables[i].name != variables[j].name
    }

    static predicate UniquelyNamed(variables: set<Variable>) {
      forall v0 <- variables, v1 <- variables :: v0.name == v1.name ==> v0 == v1
    }
  }

  datatype VariableKind = In | InOut | Out | Local | Let | Bound
  {
    predicate IsParameter() {
      this in {In, InOut, Out}
    }
    predicate IsIncomingParameter() {
      this in {In, InOut}
    }
    predicate IsOutgoingParameter() {
      this in {InOut, Out}
    }
    predicate IsAssignable() {
      this in {InOut, Out, Local}
    }
  }

  const OldPrefix: string := "old$"

  function OldName(name: string): string {
    OldPrefix + name
  }

  lemma UniqueNamesImpliesUniqueOldNames(variables: set<Variable>)
    requires Variable.UniquelyNamed(variables)
    ensures forall v0 <- variables, v1 <- variables :: OldName(v0.name) == OldName(v1.name) ==> v0 == v1
  {
    forall v0 <- variables, v1 <- variables | OldName(v0.name) == OldName(v1.name)
      ensures v0 == v1
    {
      assert v0.name == OldName(v0.name)[|OldPrefix|..];
      assert v1.name == OldName(v1.name)[|OldPrefix|..];
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
    | Block(lbl: string, stmts: List<Stmt>)
    | Call(name: string, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(v: Variable, body: Stmt)
    // Control flow
    | If(cond: Expr, thn: Stmt, els: Stmt)
    | IfCase(cases: seq<Case>)
    | Loop(lbl: string, invariants: List<AExpr>, body: Stmt)
    | Exit(lbl: string)
    | Return
    // Error reporting
    | Probe(e: Expr)
  {
    predicate ContainsAssertions() {
      match this
      case Block(_, stmts: List<Stmt>) =>
        stmts.Exists((s: Stmt) requires s < this => s.ContainsAssertions())
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
        stmts.Exists((s: Stmt) requires s < this => s.ContainsNonAssertions())
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
        v.kind == Local && LegalVariableName(v.name, localNames)
      case ValDecl(v, rhs) =>
        && v.kind == Let && LegalVariableName(v.name, localNames)
        && rhs.Type(b3, scope) == Some(v.typ)
      case Assign(lhs, rhs) =>
        && lhs in scope.Keys
        && var v := scope[lhs];
        && v.kind.IsAssignable() && rhs.Type(b3, scope) == Some(v.typ)
      case Block(lbl, stmts) =>
        LegalLabel(lbl, labels) && WellFormedStmtList(stmts, b3, scope, {}, labels + {lbl})
      case Call(name, args) =>
        exists proc <- b3.procedures ::
          && name == proc.name
          && MatchingParameters(proc.parameters, args)
          && (forall i :: 0 <= i < |args| ==> args[i].WellFormed(proc.parameters[i], b3, scope))
      case Check(cond) =>
        cond.Type(b3, scope) == Some(BoolType)
      case Assume(cond) =>
        cond.Type(b3, scope) == Some(BoolType)
      case Assert(cond) =>
        cond.Type(b3, scope) == Some(BoolType)
      case AForall(v, body) =>
        && v.kind == Bound && LegalVariableName(v.name, localNames)
        && body.WellFormed(b3, scope[v.name := v], localNames, labels)
        && !body.ContainsNonAssertions()
      case If(cond, thn, els) =>
        && cond.Type(b3, scope) == Some(BoolType)
        && thn.WellFormed(b3, scope, localNames, labels)
        && els.WellFormed(b3, scope, localNames, labels)
      case IfCase(cases) =>
        && |cases| != 0
        && forall i :: 0 <= i < |cases| ==> var cs := cases[i];
            && cs.cond.Type(b3, scope) == Some(BoolType)
            && cs.body.WellFormed(b3, scope, localNames, labels)
      case Loop(lbl, invariants, body) =>
        && LegalLabel(lbl, labels)
        && invariants.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, scope, labels))
        && body.WellFormed(b3, scope, localNames, labels + {lbl})
      case Exit(lbl) =>
        LegalLabel(lbl, labels)
      case Return =>
        true
      case Probe(e) =>
        e.Type(b3, scope).Some?
    }

    static predicate WellFormedStmtList(stmts: List<Stmt>, b3: Program, scope: Scope, localNames: set<string>, labels: set<string>) {
      match stmts
      case Nil => true
      case Cons(stmt, cont) =>
        && stmt.WellFormed(b3, scope, localNames, labels)
        && var (scope', localNames') :=
            match stmt
            case VarDecl(v) => (scope[stmt.v.name := stmt.v], localNames + {stmt.v.name})
            case ValDecl(v, _) => (scope[stmt.v.name := stmt.v], localNames + {stmt.v.name})
            case _ => (scope, localNames);
          WellFormedStmtList(cont, b3, scope', localNames', labels)
    }

    static predicate MatchingParameters(parameters: seq<Variable>, args: seq<CallArgument>) {
      && (forall i, j :: 0 <= i < j < |args| && args[i].ArgLValue? && args[j].ArgLValue? ==> args[i].name != args[j].name)
      && |args| == |parameters|
    }
  }

  const ReturnLabel: string := "_return"

  predicate LegalLabel(lbl: string, labels: set<string>) {
    lbl != ReturnLabel && lbl !in labels
  }

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed(b3: Program, scope: Scope, labels: set<string>) {
      match this
      case AExpr(e) =>
        e.Type(b3, scope) == Some(BoolType)
      case AAssertion(s) =>
        s.WellFormed(b3, scope, {}, labels) && !s.ContainsNonAssertions()
    }

    function ToCheckStmt(): Stmt {
      match this
      case AExpr(e) => Assert(e)
      case AAssertion(s) => s
    }

    function ToAssumeStmt(): Stmt {
      match this
      case AExpr(e) => Assume(e)
      case AAssertion(s) => s // TODO: need to convert these statements, too
    }
  }

  datatype CallArgument =
    | ArgExpr(e: Expr)
    | ArgLValue(name: string)
  {
    predicate WellFormed(formal: Variable, b3: Program, scope: Scope) {
      match this
      case ArgExpr(e) =>
        formal.kind == In && e.Type(b3, scope) == Some(formal.typ)
      case ArgLValue(name) =>
        && formal.kind.IsOutgoingParameter()
        && name in scope && var v := scope[name];
        && v.kind.IsAssignable() && v.typ == formal.typ
    }

    function Eval(vals: Valuation): Value
      requires ArgLValue? ==> name in vals
    {
      match this
      case ArgExpr(e) => e.Eval(vals)
      case ArgLValue(name) => vals[name]
    }
  }
  
  // Expressions

  type Expr
  {
    function Type(b3: Program, scope: Scope): Option<string>
    function Eval(vals: Valuation): Value // TODO: either make Option<Value> or require Type(...).Some?
  }
}