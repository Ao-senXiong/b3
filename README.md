# B3

An intermediate verification language

## View and build

To view and edit the sources, open this folder with VS Code.

To manage the project from the command line, see the `Makefile`. For example, to verify the code, run

```
make verify
```

## B3 documentation

### Reference manual

The B3 reference manual, _This is B3_, is written in MyST Markdown within Sphinx.

To install

    pip install sphinx
    pip install myst-parser
    pip install renku-sphinx-theme
    pip install pygments

### Other documents

[B3 concept document](doc/out/krml301.html)

To edit the documentation, use [Madoko source](doc/krml301.mdk)

About the implementation:
[B3 syntax, raw AST, and printing](doc/out/krml304.html)

## Tool stages

- Parser: input characters -> raw AST
  -- RawAst.WellFormed says whether or not raw AST is well-formed, but doesn't give good error messages
- Resolver: raw AST -> resolved AST
  -- generates a good error message if RawAst.WellFormed does not hold
  -- ensures Ast.WellFormed
- TypeChecker: operates on a well-formed resolved AST
  -- check if AST is type correct
  -- ensures TypeCorrect
- Verifier: resolved AST -> calls to Solver.{extend,prove}
- Semantics: gives co-inductive big-step semantics for raw AST (soon: resolved AST)
- Somewhere, should also do macro expansions (before Resolver, operating on raw AST) and closure lifting (probably best done on resolved AST)

