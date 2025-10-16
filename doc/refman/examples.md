# Examples

Here is a simple B3 program to whet your appetite.

```
// Here is a little comment

type List
tagger ListTag for List

function Nil(): List tag ListTag
function Cons(injective head: int, injective tail: List): List tag ListTag

function Length(list: List): int
axiom forall list: List pattern Length(list) 0 <= Length(list)

procedure TestLists(list: List) {
  var n := Length(list)
  check n != -9
}
```

Here is a longer example:

```{literalinclude} ../../test/refman/FileSystem.b3
:start-after: // BEGIN EXAMPLE
:end-before: // END EXAMPLE
```
