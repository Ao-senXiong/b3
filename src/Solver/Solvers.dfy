module Solvers {
  import opened Std.Wrappers
  import opened Basics
  import opened SolverExpr
  import Smt = SmtEngines
  import opened DeclarationMarkers

  export
    reveals SolverState, ProofResult, StackItem, SolverState.Evolves
    provides SolverState.Repr, SolverState.Valid
    provides SolverState.stack, SolverState.declarations, SolverState.additionalDeclaredNames
    reveals SolverState.IsTopMemo
    provides SolverState.Push, SolverState.Pop
    provides SolverState.DeclareType, SolverState.AddDeclarationMarker, SolverState.DeclareSymbol, SolverState.DeclareAdditionalName
    provides SolverState.AddAssumption, SolverState.Prove
    provides Smt, Basics, SolverExpr, DeclarationMarkers

  datatype ProofResult =
    | Proved
    | Unproved(reason: string)

  datatype StackItem<Memo> = StackItem(memo: Memo, decls: set<DeclarationMarker>, names: set<string>)
  
  /// This solver state can backtrack, however, it cannot spawn new SMT instances.
  /// The solver state includes a stack of (memo, marker set) pairs, which allows the solver
  /// to be shared (in a sequential fashion) among several clients. The clients then update
  /// the stack and marker set to keep track of what has been given to the underlying SMT solver.
  ///
  /// Markers are typically of the type DeclarationMarker. For situations where it's awkward for
  /// the client to create new DeclarationMarkers, there is also a set of strings that can be used
  /// instead of or in addition to the set of DeclarationMarker.
  class SolverState<Memo(==)> {
    ghost const Repr: set<object>

    const smtEngine: Smt.SolverEngine
    var stack: List<StackItem<Memo>>

    var declarations: set<DeclarationMarker>
    var additionalDeclaredNames: set<string>

    constructor (smtEngine: Smt.SolverEngine)
      requires smtEngine.Valid()
      requires smtEngine.CommandStacks == Cons(Nil, Nil)
      ensures Valid() && fresh(Repr - {smtEngine, smtEngine.process})
    {
      this.smtEngine := smtEngine;
      this.stack := Nil;
      this.declarations := {};
      this.additionalDeclaredNames := {};
      this.Repr := {this, smtEngine, smtEngine.process};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && smtEngine in Repr
      && smtEngine.process in Repr
      && this !in {smtEngine, smtEngine.process}
      && smtEngine.Valid()
      && stack.Length() + 1 == smtEngine.CommandStacks.Length()
    }

    twostate predicate Evolves()
      reads this
    {
      && old(stack) == stack
      && old(declarations) <= declarations
      && old(additionalDeclaredNames) <= additionalDeclaredNames
    }

    predicate IsTopMemo(m: Memo)
      reads this
    {
      stack.Cons? && stack.head.memo == m
    }

    method Push(memo: Memo)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == Cons(StackItem(memo, declarations, additionalDeclaredNames), old(stack))
      ensures declarations == old(declarations) && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      smtEngine.Push();
      stack := Cons(StackItem(memo, declarations, additionalDeclaredNames), stack);
    }

    method Pop()
      requires Valid() && stack.Cons?
      modifies Repr
      ensures Valid() && stack == old(stack).tail
      ensures declarations == old(stack).head.decls && additionalDeclaredNames == old(stack).head.names
    {
      smtEngine.CommandStacks.AboutDoubleCons();
      smtEngine.Pop();
      var StackItem(_, decls, names) := stack.head;
      stack := stack.tail;
      declarations := decls;
      additionalDeclaredNames := names;
    }

    method AddAssumption(expr: SExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      smtEngine.Assume(expr.ToString());
    }

    method DeclareType(decl: STypeDecl, marker: DeclarationMarker)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) + {marker} && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      smtEngine.DeclareSort(decl.name);
      declarations := declarations + {marker};
    }

    method AddDeclarationMarker(marker: DeclarationMarker)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) + {marker} && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      declarations := declarations + {marker};
    }

    method DeclareSymbol(decl: STypedDeclaration, marker: DeclarationMarker)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) + {marker} && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      DeclareSymbolByName(decl.name, SType.TypesToSExpr(decl.inputTypes), decl.typ.ToSExpr());
      declarations := declarations + {marker};
    }

    method DeclareAdditionalName(decl: STypedDeclaration, namedMarker: string)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) && additionalDeclaredNames == old(additionalDeclaredNames) + {namedMarker}
    {
      DeclareSymbolByName(decl.name, SType.TypesToSExpr(decl.inputTypes), decl.typ.ToSExpr());
      additionalDeclaredNames := additionalDeclaredNames + {namedMarker};
    }

    method DeclareSymbolByName(name: string, inputTpe: SExpr, outputTpe: SExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      smtEngine.DeclareFunction(name, inputTpe.ToString(), outputTpe.ToString());
    }

    method Prove(expr: SExpr) returns (result: ProofResult)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack)
      ensures declarations == old(declarations) && additionalDeclaredNames == old(additionalDeclaredNames)
    {
      smtEngine.Push();
      smtEngine.Assume(SExpr.Negation(expr).ToString());

      var satness := smtEngine.CheckSat();
      if satness.Failure? {
        result := Unproved(satness.error);
      } else if satness.value == "unsat" {
        result := Proved;
      } else {
        var reason := satness.value;
        var r := smtEngine.GetModel();
        if r.Success? {
          reason := reason + "\n" + r.value;
        }
        result := Unproved(reason);
      }

      smtEngine.Pop();
    }
  }
}
