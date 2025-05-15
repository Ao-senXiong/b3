module Values {
  import opened Types

  // Values

  type Value(0,!new)
  const True: Value

  predicate HasType(val: Value, typ: Type)

  type Valuation = map<string, Value>
}
