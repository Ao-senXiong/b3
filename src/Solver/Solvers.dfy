module Solvers {
  import Smt
  import Z3SmtSolver // TODO: Use solver factories?
  export
    provides Solver, Solver.Extend, Solver.Prove, Solver.Record, Solver.Empty
    reveals SolverState
    reveals Context
    provides SolverState.solver, SolverState.Valid, SolverState.assumptions
    provides SolverState.ValidFor
    provides Smt
    provides B
    provides SolverExpr

  import opened SolverExpr
  import B = Basics

  datatype ProofResult =
      Proved
    | Unproved(reason: string)
  
  datatype Context =
    | Assumption(assumed: SExpr)
    | Declaration(name: string, inputType: SExpr, outputType: SExpr)
  {
    function ToSmt(): Smt.Context {
      match this {
        case Assumption(assumed) =>
          Smt.Assumption(assumed.ToString())
        case Declaration(name, inputType, outputTpe) =>
          Smt.Declaration(name, inputType.ToString(), outputType.ToString())
      }
    }
    function ToString(): string {
      ToSmt().ToString()
    }
  }

  // This solver state can backtrack, however, it cannot spawn new Z3 instances
  class SolverState {
    ghost var assumptions: B.List<Context>
    ghost var assumptionsStacks: B.List<B.List<Context>>

    const solver: Smt.Solver

    constructor(solver: Smt.Solver)
    // Should be a fresh solver
      requires solver.CommandStacks() == B.Cons(B.Nil, B.Nil)
      requires solver.Valid()
      ensures solver == this.solver
      ensures this.Valid()
      ensures this.ValidFor(Solver.Empty())
    {
      this.solver := solver;
      this.assumptions := B.Nil;
      this.assumptionsStacks := B.Cons(B.Nil, B.Nil);
    }

    ghost predicate ValidFor(s: Solver) reads this {
      s.assumptions == this.assumptions.ToReverseSeq()
    }
    
    static ghost predicate assumptionsSyncCommands(
      assumptionsStacks: B.List<B.List<Context>>,
      commandStacks: B.List<B.List<string>>
    ) {
      || (assumptionsStacks.Nil? && commandStacks.Nil?)
      || (assumptionsStacks.Cons? && commandStacks.Cons?
        && commandStacks.head == assumptionsStacks.head.Map((a: Context) => a.ToSmt().ToString())
        && assumptionsSyncCommands(assumptionsStacks.tail, commandStacks.tail)
      )
    }

    ghost predicate Valid() reads this, solver, solver.process
    {
      solver.Valid()
      && this as object !in {solver, solver.process}
      && B.ListFlatten(assumptionsStacks) == assumptions
      && assumptionsSyncCommands(assumptionsStacks, solver.CommandStacks())
    }

    ghost predicate ValidBeforePop() reads this, solver, solver.process
    {
      solver.Valid()
      && this as object !in {solver, solver.process}
      && B.ListFlatten(assumptionsStacks) == assumptions
      && assumptionsStacks.Cons?
      && assumptionsSyncCommands(assumptionsStacks.tail, solver.CommandStacks().tail)
    }

    method Push()
      requires Valid()
      modifies this, solver, solver.process
      ensures Valid()
      ensures assumptions == old(assumptions)
      ensures assumptionsStacks.tail == old(assumptionsStacks)
    {
      solver.Push();
      assumptionsStacks := B.Cons(B.Nil, assumptionsStacks);
    }

    method Pop()
      requires ValidBeforePop()
      requires solver.CommandStacks().DoubleCons?
      modifies solver, solver.process
      modifies this
      ensures Valid()
      ensures assumptionsStacks == old(this.assumptionsStacks.tail)
    {
      solver.Pop();
      assumptions := assumptions.DropAsMuchAsHeadOf(assumptionsStacks);
      assumptionsStacks := assumptionsStacks.tail;
    }

    method AddContext(context: Context)
      requires Valid()
      modifies this, solver, solver.process
      ensures Valid()
      ensures assumptions == B.Cons(context, old(assumptions))
      ensures assumptionsStacks.head.Cons?
      ensures assumptionsStacks == old(assumptionsStacks.(
        head := B.Cons(context, assumptionsStacks.head)))
    {
      match context {
        case Declaration(name, inputTpe, outputTpe) =>
          solver.DeclareFun(name, inputTpe.ToString(), outputTpe.ToString());
        case Assumption(e) =>
          solver.Assume(e.ToString());
      }
      assumptions := B.Cons(context, assumptions);
      assumptionsStacks := assumptionsStacks.(
        head := B.Cons(context, assumptionsStacks.head));
    }

    method DeclareSymbol(name: string, inputTpe: SExpr, outputTpe: SExpr)
      requires Valid()
      modifies this, solver, solver.process
      ensures Valid()
      ensures assumptions == B.Cons(Declaration(name, inputTpe, outputTpe), old(assumptions))
      ensures assumptionsStacks.head.Cons?
      ensures assumptionsStacks == old(assumptionsStacks.(
        head := B.Cons(Declaration(name, inputTpe, outputTpe), assumptionsStacks.head)))
    {
      AddContext(Declaration(name, inputTpe, outputTpe));
    }
    // In-place extension
    method Extend(e: SExpr)
      requires Valid()
      modifies this, solver, solver.process
      ensures Valid()
      ensures assumptions == B.Cons(Assumption(e), old(assumptions))
      ensures assumptionsStacks.head.Cons?
      ensures assumptionsStacks == old(assumptionsStacks.(
        head := B.Cons(Assumption(e), assumptionsStacks.head)))
    {
      AddContext(Assumption(e));
    }

    method Prove(e: SExpr) returns (result: ProofResult )
      requires Valid()
      ensures Valid()
      modifies this, solver, solver.process
      ensures assumptions == old(assumptions)
    {
      Push();
      assert assumptionsSyncCommands(assumptionsStacks.tail, solver.CommandStacks().tail);
      Extend(SExpr.Negation(e));
      var satness := solver.CheckSat();
      if satness == "unsat" {
        result := Proved;
      } else {
        var model := solver.GetModel();
        result := Unproved(satness + "\n" + model);
      }
      Pop();
    }
  }

  datatype Solver =
    Solver(assumptions: seq<Context>)
  {
    static function Empty(): Solver {
      Solver([])
    }
    // Forking is costly as it creates a new SMT process
    // and it will replay all assumptions till then
    // but it is necessary if we plan on verifying in a previous solver state.
    method Fork() returns (newSolverState: SolverState)
      ensures fresh(newSolverState)
      ensures newSolverState.ValidFor(this)
    {
      var newSolver := Z3SmtSolver.CreateZ3Solver();
      newSolverState := new SolverState(newSolver);
      assert newSolverState.ValidFor(Solver([]));
      for i := 0 to |assumptions|
        invariant newSolverState.ValidFor(Solver(assumptions[0..i]))
        invariant newSolverState.Valid()
      {
        newSolverState.AddContext(assumptions[i]);
      }
      assert assumptions[0..|assumptions|] == assumptions;
      assert newSolverState.ValidFor(this);
    }
    method Extend(e: SExpr, s: SolverState) returns (newSolver: Solver)
      requires s.Valid()
      requires s.ValidFor(this)
      modifies s, s.solver, s.solver.process
      ensures s.ValidFor(newSolver)
      ensures s.Valid()
    {
      newSolver := Solver(assumptions + [Assumption(e)]);
      s.Extend(e);
    }
    method Prove(e: SExpr, s: SolverState)
      requires s.Valid() && s.ValidFor(this)
      modifies s, s.solver, s.solver.process
      ensures s.Valid() && s.ValidFor(this)
    {
      // TODO
      print "----- Proof obligation:\n";
      for i := 0 to |assumptions| {
        print "  ", assumptions[i], "\n";
      }
      print "  |-\n";
      print "  ", e, "\n";
      var proofResult := s.Prove(e);
      print "Result:", proofResult, "\n";
    }
    method Record(e: SExpr) returns (solver: Solver)
    { solver := this; } // TODO
  }
}
