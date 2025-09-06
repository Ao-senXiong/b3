# Statements

Statements and expressions in B3 are self-terminating, so there are no semi-colons.

```
Stmt ::=
  | VarDecl
  | Assign
  | BlockStmt
  | Call
  // assertions
  | Check
  | Assume
  | Assert
  | AForall
  // control flow
  | Choose
  | If
  | IfCase
  | Loop
  | LabeledStmt
  | Exit
  | Return
  // error reporting
  | Probe
```

## Variable declarations

```
VarDecl ::=
  ( var | val ) Identifier [ ":" Type ] [ ":=" Expression ]
```

A declaration using `var` introduces a mutable local variable, whereas `val`
introduces an immutable local variable. A mutable variable that is never updated
is semantically equivalent to an immutable variable. However, the body of a `forall`
statements is not allowed to declare mutable variables.

The variable declaration is allowed to omit one of `: Type` or `:= Expression`,
but not both. If the type is omitted, it is determined from the given expression.
If the expression is omitted, the variable is initialized with an arbitrary value
of its type.

The variable remains in scope until the end of the enclosing block.

A variable is allowed to shadow previously declared variables with the same name.

## Assignment statements

```
Assign ::=
  Identifier ":=" Expression
```

The identifier must be a mutable variable.

## Block statements

```
BlockStmt ::=
  "{" Stmt* "}"
```

## Call statement

```
Call ::=
  Identifier "(" CallArgument ")"
CallArgument ::=
  | Expression
  | ( "inout" | "out" ) Identifier
```

A call statement invokes a procedure. The argument mode (in, inout, or out) of each parameter
is explicitly repeated at the call site (where the absence of `inout` and `out` indicates an
in-argument).

The types of the actual arguments must be the same as for the corresponding formal parameters.

The variables given as inout- and out-arguments must be distinct mutable variables.

## Check statements

```
Check ::=
  check Expression
```

A check statement prescribes a proof obligation. It is an error if control flow can reach a `check`
statement whose expression can evaluate to `false`.

The given expression 

## Assume statements

```
Assume ::=
  assume Expression
```

## Assert statements

```
Assert ::=
  assert Expression
```

A statement `assert E` is equivalent to the statement sequence `check E assume E`.

## Forall statements

```
AForall ::=
  forall Identifier ":" Type
  BlockStmt
```

TODO: description

## Choose statements

```
Choose ::=
  choose BlockStmt ( or BlockStmt )*
```

TODO: description

## If statements

```
If ::=
  if Expression BlockStmt [ else IfContinuation ]
IfContinuation ::=
  | BlockStmt
  | If
  | IfCase
```

TODO: description

## If-case statements

```
IfCase ::=
  if Case+
Case ::=
  case Expression BlockStmt
```

TODO: description

## Loops

```
Loop ::=
  loop Invariant* BlockStmt
Invariant ::=
  invariant AExpression
```

TODO: description

## Labeled statements

```
LabeledStmt ::=
  Identifier ":" ( BlockStmt | Loop )
```

TODO: description

## Exit statements

```
Exit ::=
  exit [ Identifier ]
```

An exit statement terminates a statement abruptly, transferring control out
of the enclosing statement labeled with the given label. If the label is omitted,
the statement transfers control out of the enclosing loop (which need not be labeled).

## Return statements

```
Return ::=
  return
```

A return statement terminates a procedure body abruptly, transferring control out
of the enclosing procedure body. It is as if the procedure body were labeled and
the return statement performs an `exit` to that label.

## Probe statements

```
Probe ::=
  probe Expression
```

TODO: description
