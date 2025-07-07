module Resolver {
  export
    provides Resolve
    provides Wrappers, Raw, Ast

  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import Raw = RawAst
  import opened Ast

  method Resolve(b3: Raw.Program) returns (r: Result<Ast.Program, string>)
    ensures r.Success? ==> b3.WellFormed() && r.value.WellFormed()
  {
    var boolType := new Type(BoolTypeName);
    var intType := new Type(IntTypeName);
    var typeMap := map[BoolTypeName := boolType, IntTypeName := intType];
    for n := 0 to |b3.types|
      // typeMap maps built-in types and the user-defined types seen so far to distinct type-declaration objects
      invariant typeMap.Keys == BuiltInTypes + set typename <- b3.types[..n]
      invariant MapIsInjective(typeMap)
      // typeMap organizes type-declaration objects correctly according to their names
      invariant forall typename <- typeMap.Keys :: typeMap[typename].Name == typename
      // no user-defined type seen so far uses the name of a built-in type
      invariant forall typename <- b3.types[..n] :: typename !in BuiltInTypes
      // the user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.types[i] != b3.types[j]
    {
      var name := b3.types[n];
      if name in typeMap.Keys {
        return Failure("duplicate type name: " + name);
      }
      var typ := new Type(name);
      typeMap := typeMap[name := typ];
    }

    var procMap: map<string, Procedure> := map[];
    for n := 0 to |b3.procedures|
      // procMap maps the user-defined procedures seen so far to distinct procedure-declaration objects
      invariant procMap.Keys == set proc <- b3.procedures[..n] :: proc.name
      invariant MapIsInjective(procMap)
      // procMap organizes procedure-declaration objects correctly according to their names
      invariant forall procname <- procMap.Keys :: procMap[procname].Name == procname
      // user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.procedures[i].name != b3.procedures[j].name
      // the procedures seen so far are well-formed
      invariant forall proc <- b3.procedures[..n] :: proc.WellFormed(b3)
    {
      var proc := b3.procedures[n];
      var name := proc.name;
      if name in procMap.Keys {
        return Failure("duplicate procedure name: " + name);
      }
      var rproc :- ResolveProcedure(proc, b3);
      procMap := procMap[name := rproc];
    }

    var r3 := Program(typeMap.Values, procMap.Values);

    return Success(r3);
  }

  method ResolveProcedure(proc: Raw.Procedure, b3: Raw.Program) returns (r: Result<Procedure, string>)
    ensures r.Success? ==> proc.WellFormed(b3)
    ensures r.Success? ==> r.value.Name == proc.name
  {
    if i, j :| 0 <= i < j < |proc.parameters| && proc.parameters[i].name == proc.parameters[j].name {
      return Failure("duplicate parameter name: " + proc.parameters[i].name);
    }

/*
    // TODO: remove 
      && var preScope := map p <- parameters | p.kind.IsIncomingParameter() :: p.name := p;
      && pre.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, preScope, {}))
      && var scope := map p <- parameters :: p.name := p;
      && post.Forall((ae: AExpr) requires ae < this => ae.WellFormed(b3, scope, {}))
      && var localNames := set p <- parameters | p.kind.IsOutgoingParameter() :: p.name;
      && (body == None || body.value.WellFormed(b3, scope, localNames, {}))
*/


    var rproc := new Procedure(proc.name, [], [], []); // TODO: other parameters
    assume {:axiom} proc.WellFormed(b3); // TODO
    return Success(rproc);
  }
}