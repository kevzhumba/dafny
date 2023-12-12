
// InductionVsCoinduction.dfy

ghost function Up(n: int): Stream<int>
{
  SCons(n, Up(n + 1))
}

ghost function FivesUp(n: int): Stream<int>
  decreases 4 - (n - 1) % 5
{
  if n % 5 == 0 then
    SCons(n, FivesUp(n + 1))
  else
    FivesUp(n + 1)
}

greatest predicate Pos(s: Stream<int>)
{
  match s
  case SNil =>
    true
  case SCons(x, rest) =>
    x > 0 &&
    Pos(rest)
}

ghost function SAppend(xs: Stream, ys: Stream): Stream
{
  match xs
  case SNil =>
    ys
  case SCons(x, rest) =>
    SCons(x, SAppend(rest, ys))
}

lemma {:induction false} SAppendIsAssociativeK(k: nat, a: Stream, b: Stream, c: Stream)
  ensures SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c))
  decreases k
{
  match a {
    case {:split false} SNil =>
    case {:split false} SCons(h, t) =>
      if k > 0 {
        SAppendIsAssociativeK(k - 1, t, b, c);
      }
  }
}

lemma SAppendIsAssociative(a: Stream, b: Stream, c: Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
{
  forall k: nat | true {
    SAppendIsAssociativeK(k, a, b, c);
  }
  assert forall k: nat {:autotriggers false} :: SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c));
}

greatest lemma {:induction false} SAppendIsAssociativeC(a: Stream, b: Stream, c: Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
{
  match a {
    case {:split false} SNil =>
    case {:split false} SCons(h, t) =>
      SAppendIsAssociativeC(t, b, c);
  }
}

greatest lemma SAppendIsAssociative_Auto(a: Stream, b: Stream, c: Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
{
}

greatest lemma {:induction false} UpPos(n: int)
  requires n > 0
  ensures Pos(Up(n))
{
  UpPos(n + 1);
}

greatest lemma UpPos_Auto(n: int)
  requires n > 0
  ensures Pos(Up(n))
{
}

greatest lemma {:induction false} FivesUpPos(n: int)
  requires n > 0
  ensures Pos(FivesUp(n))
  decreases 4 - (n - 1) % 5
{
}

greatest lemma FivesUpPos_Auto(n: int)
  requires n > 0
  ensures Pos(FivesUp(n))
  decreases 4 - (n - 1) % 5
{
}

codatatype Stream<T> = SNil | SCons(head: T, tail: Stream<T>)
