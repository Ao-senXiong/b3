module Types {
  // Types

  type Type = string

  const BoolType := "bool"
  const IntType := "int"
  const BuiltInTypes: set<Type> := {BoolType, IntType}
}