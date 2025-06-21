module Values {
  import opened Types

  // Values

  type Value(0,!new) = int // TODO
  const True: Value

  predicate HasType(val: Value, typ: TypeName) {
    true // TODO
  }

  type Valuation = map<string, Value>
}
