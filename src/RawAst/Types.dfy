module Types {
  // Types

  type TypeName = string

  const BoolTypeName := "bool"
  const IntTypeName := "int"
  const BuiltInTypes: set<TypeName> := {BoolTypeName, IntTypeName}

  class Type {
    const Name: string
    
    constructor (name: string)
      ensures Name == name
    {
      Name := name;
    }
  }
}