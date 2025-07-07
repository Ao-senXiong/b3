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
    if p :| p in proc.parameters && !Raw.LegalVariableName(p.name, {}) {
      return Failure("illegal parameter name: " + p.name);
    }

    if p :| p in proc.parameters && !b3.IsType(p.typ) {
      return Failure("unknown type: " + p.typ);
    }

    if i, j :| 0 <= i < j < |proc.parameters| && proc.parameters[i].name == proc.parameters[j].name {
      return Failure("duplicate parameter name: " + proc.parameters[i].name);
    }

    var preScope := set p <- proc.parameters | p.mode.IsIncoming() :: p.name;
    var bodyScope := set p <- proc.parameters :: p.name;
    var postScope := bodyScope + (set p <- proc.parameters | p.mode == Raw.InOut :: Raw.OldName(p.name));

    if ae :| ae in proc.pre && !ae.WellFormed(b3, preScope) {
      return Failure("ill-formed precondition of procedure " + proc.name);
    }

    if ae :| ae in proc.post && !ae.WellFormed(b3, postScope) {
      return Failure("ill-formed postcondition of procedure " + proc.name);
    }

    if proc.body.Some? {
      if !proc.body.value.WellFormed(b3, bodyScope, {}, false) {
        return Failure("ill-formed body of procedure " + proc.name);
      }
    }

    var rproc := new Procedure(proc.name, [], [], []); // TODO: other parameters
    assert proc.WellFormed(b3) by {
      assert forall p <- proc.parameters :: Raw.LegalVariableName(p.name, {}) && b3.IsType(p.typ);
      assert Parameter.UniqueNames(proc.parameters);
      assert forall ae <- proc.pre :: ae.WellFormed(b3, preScope);
      assert forall ae <- proc.post :: ae.WellFormed(b3, postScope);
      assert proc.body == None || proc.body.value.WellFormed(b3, bodyScope, {}, false);
    }
    return Success(rproc);
  }
}