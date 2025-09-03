module Incarnations {
  import opened Basics
  import opened Ast
  import opened SolverExpr
  import Types
  import RSolvers

  export
    reveals DeclMappings
    provides DeclMappings.Type2SType, DeclMappings.Type2STypeWithMap
    provides Incarnations
    provides Incarnations.Empty, Incarnations.DeclMap
    provides Incarnations.Update, Incarnations.Reserve, Incarnations.Variables, Incarnations.DomainRestrict
    provides Incarnations.Set, Incarnations.CreateSubMap
    provides Incarnations.Get, Incarnations.REval, Incarnations.SubstituteVariable, Incarnations.Type2SType
    provides Types, Ast, SolverExpr, RSolvers

  type RExpr = RSolvers.RExpr

  datatype DeclMappings = DeclMappings(typeMap: map<Types.TypeDecl, STypeDecl>, functionMap: map<Function, STypedDeclaration>)
  {
    function Type2SType(typ: Type): SType {
      Type2STypeWithMap(typ, typeMap)
    }

    static function Type2STypeWithMap(typ: Type, typeMap: map<Types.TypeDecl, STypeDecl>): SType {
      match typ
      case BoolType => SBool
      case IntType => SInt
      case UserType(decl) =>
        assume {:axiom} decl in typeMap;
        var sTypeDecl := typeMap[decl];
        SUserType(sTypeDecl)
    }
  }

  datatype Incarnations = Incarnations(nextSequenceCount: map<string, nat>, m: map<Variable, SVar>, declMap: DeclMappings)
  {
    static function Empty(declMap: DeclMappings): Incarnations {
      Incarnations(map[], map[], declMap)
    }

    function DeclMap(): DeclMappings {
      declMap
    }

    function Type2SType(typ: Type): SType {
      declMap.Type2SType(typ)
    }

    function Variables(): set<Variable> {
      m.Keys
    }

    function Get(v: Variable): SVar {
      assume {:axiom} v in m; // TODO
      m[v]
    }

    // `Set` is intended to be used only during custom initializations of an Incarnations.
    function Set(v: Variable, sv: SVar): Incarnations {
      this.(nextSequenceCount := map[v.name := 0] + nextSequenceCount, m := m[v := sv])
    }

    // `Set` is intended to be used only during custom initializations of an Incarnations.
    function CreateSubMap(customMap: map<Variable, SVar>): Incarnations {
      Incarnations(nextSequenceCount, customMap, declMap)
    }

    method ReserveAux(v: Variable) returns (next: nat, x: SVar) {
      var name := v.name;
      if name in nextSequenceCount.Keys {
        var n := nextSequenceCount[name];
        name := name + "%" + Int2String(n);
        next := n + 1;
      } else {
        next := 0;
      }
      x := new SVar(name, declMap.Type2SType(v.typ));
    }

    method Reserve(v: Variable) returns (incarnations: Incarnations, x: SVar) {
      var nextSequenceNumber;
      nextSequenceNumber, x := ReserveAux(v);
      incarnations := this.(nextSequenceCount := nextSequenceCount[v.name := nextSequenceNumber]);
    }

    method Update(v: Variable) returns (incarnations: Incarnations, x: SVar) {
      var nextSequenceNumber;
      nextSequenceNumber, x := ReserveAux(v);
      incarnations := this.(nextSequenceCount := nextSequenceCount[v.name := nextSequenceNumber], m := m[v := x]);
    }

    function DomainRestrict(variables: set<Variable>): Incarnations {
      var m' := map v <- m.Keys | v in variables :: m[v];
      this.(m := m')
    }

    method CreateForBoundVariables(expr: Expr) returns (r: Incarnations)
      decreases expr
    {
      r := this;
      match expr
      case BLiteral(_) =>
      case ILiteral(_) =>
      case CustomLiteral(_, _) =>
      case IdExpr(_) =>
      case OperatorExpr(_, args) =>
        for i := 0 to |args| {
          r := r.CreateForBoundVariables(args[i]);
        }
      case FunctionCallExpr(_, args) =>
        for i := 0 to |args| {
          r := r.CreateForBoundVariables(args[i]);
        }
      case LabeledExpr(_, body) =>
        r := r.CreateForBoundVariables(body);
      case LetExpr(v, rhs, body) =>
        r := r.CreateForBoundVariables(rhs);
        expect v !in r.m.Keys;
        var sVar;
        r, sVar := Update(v);
        r := r.CreateForBoundVariables(body);
      case QuantifierExpr(_, v, patterns, body) =>
        expect v !in r.m.Keys;
        var sVar;
        r, sVar := Update(v);
        for i := 0 to |patterns| {
          var pattern := patterns[i];
          for j := 0 to |pattern.exprs| {
            r := r.CreateForBoundVariables(pattern.exprs[j]);
          }
        }
        r := r.CreateForBoundVariables(body);
    }

    // Create SVar's for the bound variables in "expr" and then substitute these and the other incarnations
    // into "expr".
    method REval(expr: Expr) returns (r: RSolvers.RExpr)
      requires expr.WellFormed()
    {
      var incarnations := CreateForBoundVariables(expr);
      r := incarnations.Substitute(expr);
    }

    function SubstituteVariable(v: Variable): SVar {
      assume {:axiom} v in m; // TODO
      m[v]
    }

    function Substitute(expr: Expr): RSolvers.RExpr
      requires expr.WellFormed()
    {
      match expr
      case BLiteral(value) => RExpr.Boolean(value)
      case ILiteral(value) => RExpr.Integer(value)
      case CustomLiteral(s, typ) => RExpr.CustomLiteral(s, declMap.Type2SType(typ))
      case IdExpr(v) =>
        var sv := SubstituteVariable(v);
        RExpr.Id(sv)
      case OperatorExpr(op, args) =>
        var rArgs := SubstituteList(args);
        match op {
          case IfThenElse =>
            RExpr.IfThenElse(rArgs[0], rArgs[1], rArgs[2])
          case Neq =>
            var eq := RExpr.FuncAppl(RExpr.Operator2ROperator(Operator.Eq), rArgs);
            RExpr.FuncAppl(RExpr.Operator2ROperator(Operator.LogicalNot), [eq])
          case _ =>
            RExpr.FuncAppl(RExpr.Operator2ROperator(op), rArgs)
        }
      case FunctionCallExpr(func, args) =>
        var rArgs := SubstituteList(args);
        assume {:axiom} func in declMap.functionMap;
        RExpr.FuncAppl(RSolvers.UserDefinedFunction(declMap.functionMap[func]), rArgs)
      case LabeledExpr(_, body) =>
        // TODO: do something with the label
        Substitute(body)
      case LetExpr(v, rhs, body) =>
        assume {:axiom} v in m;
        var sVar := m[v];
        RExpr.LetExpr(sVar, Substitute(rhs), Substitute(body))
      case QuantifierExpr(univ, v, patterns, body) =>
        assume {:axiom} v in m;
        var sVar := m[v];
        var trs := SubstitutePatterns(patterns);
        var b := Substitute(body);
        RExpr.QuantifierExpr(univ, sVar, trs, b)
    }

    function SubstituteList(exprs: seq<Expr>): seq<RSolvers.RExpr>
      requires forall expr <- exprs :: expr.WellFormed()
      ensures |SubstituteList(exprs)| == |exprs|
    {
      if exprs == [] then
        []
      else
        [Substitute(exprs[0])] + SubstituteList(exprs[1..])
    }

    function SubstitutePatterns(patterns: seq<Pattern>): seq<RSolvers.RPattern>
      requires forall tr <- patterns :: tr.WellFormed()
    {
      if patterns == [] then
        []
      else
        assert patterns[0].WellFormed();
        [RSolvers.RPattern(SubstituteList(patterns[0].exprs))] + SubstitutePatterns(patterns[1..])
    }
  }

}