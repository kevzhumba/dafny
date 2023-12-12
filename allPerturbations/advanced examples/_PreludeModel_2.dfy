
// PreludeModel.dfy


module Sequence {
  function Length<A>(s: T<A>): int
  {
    match s
    case Nil =>
      0
    case Cons(_ /* _v0 */, s) =>
      1 + Length(s)
  }

  lemma lemma_LengthGe0<A>(s: T<A>)
    ensures 0 <= Length(s)
  {
  }

  datatype T<A> = Nil | Cons(head: T, tail: T<T>)
}
