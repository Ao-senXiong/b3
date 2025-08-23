module Types {
  // Types

  type TypeName = string

  const BoolTypeName := "bool"
  const IntTypeName := "int"
  const BuiltInTypes: set<TypeName> := {BoolTypeName, IntTypeName}

  datatype Type =
    | BoolType
    | IntType
    | UserType(decl: TypeDecl)
  {
    function ToString(): string {
      match this
      case BoolType => BoolTypeName
      case IntType => IntTypeName
      case UserType(decl) => decl.Name
    }
  }

  class TypeDecl {
    const Name: string
    
    constructor (name: string)
      ensures Name == name
    {
      Name := name;
    }
  }
}