# Simple examples

Here is a simple B3 program to whet your appetite.

```
// Here is a little comment

type List
tagger ListTag for List

function Nil(): List tag ListTag
function Cons(injective head: int, injective tail: List): List tag ListTag

function Length(list: List): int
axiom forall list: List pattern Length(list) :: 0 <= Length(list)

procedure TestLists(list: List) {
  var n := Length(list)
  check n != -9
}
```

A to-do item for this documentation is to also make inline code, like `check x < y`,
be processed by pygments syntax highlighting.
