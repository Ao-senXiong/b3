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
    ensures r.Success? ==> b3.WellFormed()
  {
    var boolType := new Type(BoolTypeName);
    var intType := new Type(IntTypeName);
    var typeMap := map[BoolTypeName := boolType, IntTypeName := intType];
    for n := 0 to |b3.types|
      invariant BuiltInTypes <= typeMap.Keys
      invariant forall i :: 0 <= i < n ==> b3.types[i] in typeMap.Keys && b3.types[i] !in BuiltInTypes
      invariant MapIsInjective(typeMap)
      invariant forall i, j :: 0 <= i < j < n ==> b3.types[i] != b3.types[j]
    {
      var typename := b3.types[n];
      if typename in typeMap.Keys {
        return Failure("duplicate type name: " + typename);
      }
      var typ := new Type(typename);
      typeMap := typeMap[typename := typ];
    }
    assert forall typ <- b3.types :: typ !in BuiltInTypes;
    assert forall i, j :: 0 <= i < j < |b3.types| ==> b3.types[i] != b3.types[j];

    if |b3.procedures| == 0 { // TODO
      return Success(Program(typeMap.Values, {}));
    }

    return Failure("good so far, but resolver is not yet fully implemented");
  }
}