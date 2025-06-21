module Resolver {
  export
    provides Resolve
    provides Wrappers, Raw, Ast

  import opened Std.Wrappers
  import Types
  import Raw = RawAst
  import Ast

  method Resolve(b3: Raw.Program) returns (r: Result<Ast.Program, string>)
    ensures r.Success? ==> b3.WellFormed()
  {
    var types := {};
    for i := 0 to |b3.types| {
      var typename := b3.types[i];
      var typ := new Types.Type(typename);
      types := types + {typ};
    }

    return Failure("good so far, but resolver is not yet fully implemented");
  }
}