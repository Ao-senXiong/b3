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
      // invariants about typeMap
      invariant typeMap.Keys == BuiltInTypes + set typename <- b3.types[..n]
      invariant MapIsInjective(typeMap)
      // invariants related to showing we've checked the conditions of RawAst well-formedness
      invariant forall typename <- b3.types[..n] :: typename !in BuiltInTypes
      invariant forall i, j :: 0 <= i < j < n ==> b3.types[i] != b3.types[j]
      // invariants related to showing that the resolved declarations are well-formed
      invariant BuiltInTypes <= (set typ: Type <- typeMap.Values :: typ.Name)
      invariant forall typename <- typeMap.Keys :: typeMap[typename].Name == typename
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
      // invariants about procMap
      invariant procMap.Keys == set proc <- b3.procedures[..n] :: proc.name
      invariant MapIsInjective(procMap)
      // invariants related to showing we've checked the conditions of RawAst well-formedness
      invariant forall i, j :: 0 <= i < j < n ==> b3.procedures[i].name != b3.procedures[j].name
      invariant forall proc <- b3.procedures[..n] :: proc.WellFormed(b3)
      // invariants related to showing that the resolved declarations are well-formed
      invariant forall procname <- procMap.Keys :: procMap[procname].Name == procname
    {
      var proc := b3.procedures[n];
      var name := proc.name;
      if name in procMap.Keys {
        return Failure("duplicate procedure name: " + name);
      }
      var rproc := new Procedure(name, [], Nil, Nil); // TODO: other parameters
      procMap := procMap[name := rproc];
      assume {:axiom} proc.WellFormed(b3); // TODO
    }

    var r3 := Program(typeMap.Values, procMap.Values);

    return Success(r3);
  }
}