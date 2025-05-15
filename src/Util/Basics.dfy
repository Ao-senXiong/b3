module Basics {
  datatype Option<X> = None | Some(value: X)

  datatype List<X> = Nil | Cons(head: X, tail: List<X>)
  {
    predicate Forall(p: X --> bool)
      requires forall x: X :: x < this ==> p.requires(x)
    {
      match this
      case Nil => true
      case Cons(x, tail) => p(x) && tail.Forall(p)
    }

    predicate Exists(p: X --> bool)
      requires forall x: X :: x < this ==> p.requires(x)
    {
      match this
      case Nil => false
      case Cons(x, tail) => p(x) || tail.Forall(p)
    }

    function Map<Y>(f: X -> Y): List<Y> {
      match this
      case Nil => Nil
      case Cons(x, tail) => Cons(f(x), tail.Map(f))
    }
  }

  function MapProject<X, Y>(m: map<X, Y>, s: set<X>): map<X, Y> {
    map x | x in m && x in s :: m[x]
  }
}
