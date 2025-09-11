// This module is responsible for
//   * turning injective function parameters into inverse functions and their corresponding axioms
//   * creating a tag constant (nullary function) for every tagged function, along with its definition axiom
//   * declaring a tag axiom for each tagged function

module FunctionDesugaring {
  import opened Ast
  import opened Std.Wrappers
  import opened Basics

  export
    provides Desugar
    provides Ast, Wrappers

  method Desugar(b3: Program) returns (r: Result<Program, string>)
    requires b3.WellFormed()
    modifies b3.functions
    ensures r.Success? ==> var r3 := r.value;
      && b3.types == r3.types
      && b3.functions <= r3.functions
      && b3.axioms <= r3.axioms
      && b3.procedures == r3.procedures
      && r3.WellFormed()
  {
    var functions := b3.functions;
    var axioms := b3.axioms;

    for i := 0 to |b3.functions|
      invariant GoodExtension(b3.functions, b3.axioms, functions, axioms)
    {
      var func := b3.functions[i];
      var rr :- AddInverseFunctions(func, b3.functions, b3.axioms, functions, axioms);
      functions, axioms := rr.0, rr.1;
      if func.Tag.Some? {
        rr :- AddFunctionTag(func, b3.functions, b3.axioms, functions, axioms);
        functions, axioms := rr.0, rr.1;
      }
    }

    return Success(Program(b3.types, functions, axioms, b3.procedures));
  }

  ghost predicate GoodExtension(origFunctions: seq<Function>, origAxioms: seq<Axiom>, functions: seq<Function>, axioms: seq<Axiom>)
    reads functions
  {
    // the new extends the old
    && origFunctions <= functions
    && origAxioms <= axioms
    // properies needed to show the new program is well-formed
    && (forall func0 <- functions, func1 <- functions :: func0.Name == func1.Name ==> func0 == func1)
    && (forall func <- functions :: func.WellFormed())
    && (forall axiom <- axioms :: axiom.WellFormed())
  }

  method AddInverseFunctions(func: Function, ghost origFunctions: seq<Function>, ghost origAxioms: seq<Axiom>,
                             functions_in: seq<Function>, axioms_in: seq<Axiom>)
      returns (r: Result<(seq<Function>, seq<Axiom>), string>)
    requires func in origFunctions
    requires GoodExtension(origFunctions, origAxioms, functions_in, axioms_in)
    modifies func`ExplainedBy
    ensures r.Success? ==> GoodExtension(origFunctions, origAxioms, r.value.0, r.value.1)
  {
    var functions, axioms := functions_in, axioms_in;

    for j := 0 to |func.Parameters|
      invariant GoodExtension(origFunctions, origAxioms, functions, axioms)
    {
      var param := func.Parameters[j];
      if param.injective {
        var name := CombineNames(func.Name, param.name);
        if exists f <- functions :: f.Name == name { // TODO: improve the efficiency of this; there may be a lot of functions in the input, so this matters
          var msg: string := "function '" + name + "' generated from injective function parameter '" + param.name + "' clashes with an already declared function with that name";
          return Result<(seq<Function>, seq<Axiom>), string>.Failure(msg);
        }
        var parameter := new FParameter("subject", false, func.ResultType);
        var inverseFunction := new Function(name, [parameter], param.typ, None);
        functions := functions + [inverseFunction];

        // injectivity axiom:
        //
        // axiom explains F
        //   forall x: X, y: Y pattern F(x, y)
        //     F.x(F(x, y)) == x
        var boundVars, pattern, lhs := GenerateAxiomPieces(func, inverseFunction);
        var rhs := IdExpr(boundVars[j]);
        var axiom := AssembleAxiom(func, boundVars, pattern, lhs, rhs);
        axioms := axioms + [axiom];
      }
    }

    return Success((functions, axioms));
  }

  method AddFunctionTag(func: Function, ghost origFunctions: seq<Function>, ghost origAxioms: seq<Axiom>,
                        functions_in: seq<Function>, axioms_in: seq<Axiom>)
      returns (r: Result<(seq<Function>, seq<Axiom>), string>)
    requires func in origFunctions && func.WellFormed() && func.Tag.Some?
    requires GoodExtension(origFunctions, origAxioms, functions_in, axioms_in)
    modifies func`ExplainedBy
    ensures r.Success? ==> GoodExtension(origFunctions, origAxioms, r.value.0, r.value.1)
  {
    var functions, axioms := functions_in, axioms_in;

    var name := CombineNames(func.Name, "tag");
    if exists f: Function <- functions :: f.Name == name { // TODO: improve the efficiency of this; there may be a lot of functions in the input, so this matters
      var msg: string := "function '" + name + "' generated from the `tag` clause of function '" + func.Name + "' clashes with an already declared function with that name";
      return Result<(seq<Function>, seq<Axiom>), string>.Failure(msg);
    }

    // function F.tag(): tag { %tag }
    var Ftag := new Function(name, [], Types.TagType, None);
    Ftag.Definition := Some(FunctionDefinition([], CustomLiteral("%tag", Types.TagType)));
    functions := functions + [Ftag];

    // tag declarations, here shown for function F(x: X, y: Y): S tag G
    // axiom explains F
    //   forall x: X, y: Y pattern F(x, y)
    //     G(F(x, y)) == F.tag()
    var boundVars, pattern, lhs := GenerateAxiomPieces(func, func.Tag.value);
    var rhs := FunctionCallExpr(Ftag, []);
    var axiom := AssembleAxiom(func, boundVars, pattern, lhs, rhs);
    axioms := axioms + [axiom];

    return Success((functions, axioms));
  }

  // Given "func" as "function F(x: X, y: Y): S", generate
  //     * boundVars -- a list of fresh bound variables:  x: X, y: Y
  //     * pattern -- pattern F(x, y)
  //     * lhs -- wrapper(F(x, y))
  method GenerateAxiomPieces(func: Function, wrapper: Function) returns (boundVars: seq<Variable>, pattern: Pattern, lhs: Expr)
    requires |wrapper.Parameters| == 1
    ensures |boundVars| == |func.Parameters| && pattern.WellFormed() && lhs.WellFormed()
  {
    boundVars := [];
    for n := 0 to |func.Parameters|
      invariant |boundVars| == n
    {
      var param := func.Parameters[n];
      var v := new LocalVariable(param.name, false, param.typ);
      boundVars := boundVars + [v];
    }

    var Fxy := FunctionCallExpr(func, SeqMap(boundVars, (v: Variable) => IdExpr(v)));
    pattern := Pattern([Fxy]);
    lhs := FunctionCallExpr(wrapper, [Fxy]);
  }

  // Generate:
  //
  //     axiom explains func
  //       forall boundVars
  //         pattern
  //         lhs == rhs
  //
  // and add this axiom to func.ExplainedBy.
  method AssembleAxiom(func: Function, boundVars: seq<Variable>, pattern: Pattern, lhs: Expr, rhs: Expr) returns (axiom: Axiom)
    requires pattern.WellFormed() && lhs.WellFormed() && rhs.WellFormed()
    modifies func`ExplainedBy
    ensures axiom.WellFormed()
  {
    var body := OperatorExpr(Operator.Eq, [lhs, rhs]);
    var q;
    if |boundVars| == 0 {
      q := body;
    } else {
      q := QuantifierExpr(true, boundVars[0]/*TODO: use all the variables*/, [pattern], body);
    }

    axiom := new Axiom([func], q);
    func.ExplainedBy := func.ExplainedBy + [axiom];
  }

  function CombineNames(base: string, member: string): string {
    base + "." + member
  }
}