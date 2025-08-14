module Solvers {
  import opened Std.Wrappers
  import opened Basics
  import opened SolverExpr
  import Smt

  export
    reveals SolverState, ProofResult
    provides SolverState.Repr, SolverState.Valid
    provides SolverState.memos, SolverState.declarations
    reveals SolverState.IsTopMemo
    provides SolverState.Push, SolverState.Pop
    provides SolverState.DeclareSymbol, SolverState.AddAssumption, SolverState.Prove
    provides Smt, Basics, SolverExpr

  datatype ProofResult =
    | Proved
    | Unproved(reason: string)
  
  /// This solver state can backtrack, however, it cannot spawn new SMT instances.
  /// The solver state includes a stack of memos, which allows the solver to be shared
  /// (in a sequential fashion) among several clients. The clients then update the stack
  /// of memos to keep track of what has been given to the underlying SMT solver.
  class SolverState<Memo(==)> {
    ghost const Repr: set<object>

    const smtEngine: Smt.SolverEngine
    var memos: List<(Memo, set<STypedDeclaration>)> // TODO: rename this field

    function CurrentMemo(): Option<Memo>
      reads this
    {
      if memos == Nil then None else Some(memos.head.0)
    }

    var declarations: set<STypedDeclaration>

    constructor (smtEngine: Smt.SolverEngine)
      requires smtEngine.Valid() && smtEngine.CommandStacks() == Cons(Nil, Nil)
      ensures Valid() && fresh(Repr - {smtEngine, smtEngine.process})
    {
      this.smtEngine := smtEngine;
      this.memos := Nil;
      this.declarations := {};
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
      && memos.Length() + 1 == smtEngine.CommandStacks().Length()
    }

    predicate IsTopMemo(m: Memo)
      reads this
    {
      memos.Cons? && memos.head.0 == m
    }

    method Push(memo: Memo)
      requires Valid()
      modifies Repr
      ensures Valid() && memos == Cons((memo, declarations), old(memos))
    {
      smtEngine.Push();
      memos := Cons((memo, declarations), memos);
    }

    method Pop()
      requires Valid() && memos.Cons?
      modifies Repr
      ensures Valid() && memos == old(memos).tail
    {
      smtEngine.CommandStacks().AboutDoubleCons();
      smtEngine.Pop();
      var (_, decls) := memos.head;
      memos := memos.tail;
      declarations := decls;
    }

    method AddAssumption(expr: SExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && memos == old(memos)
    {
      smtEngine.Assume(expr.ToString());
    }

    method DeclareSymbol(decl: STypedDeclaration)
      requires Valid()
      modifies Repr
      ensures Valid() && memos == old(memos)
    {
      var (inputTypes, outputType) := decl.typ.SplitInputsOutput();
      DeclareSymbolByName(decl.name, SType.TypesToSExpr(inputTypes), outputType.ToSExpr());
      declarations := declarations + {decl};
    }

    method DeclareSymbolByName(name: string, inputTpe: SExpr, outputTpe: SExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && memos == old(memos)
    {
      smtEngine.DeclareFun(name, inputTpe.ToString(), outputTpe.ToString());
    }

    method Prove(expr: SExpr) returns (result: ProofResult)
      requires Valid()
      modifies Repr
      ensures Valid() && memos == old(memos)
    {
      smtEngine.Push();
      smtEngine.Assume(SExpr.Negation(expr).ToString());
      var satness := smtEngine.CheckSat();
      if satness == "unsat" {
        result := Proved;
      } else {
        var model := smtEngine.GetModel();
        result := Unproved(satness + "\n" + model);
      }
      smtEngine.Pop();
    }
  }
}
