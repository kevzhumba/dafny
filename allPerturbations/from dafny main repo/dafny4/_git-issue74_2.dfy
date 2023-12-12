
// git-issue74.dfy

function {:opaque} f(x: int): int
{
  x
}

lemma L()
  ensures forall x: int :: f(x) == x
{
  forall x: int | true
    ensures f(x) == x
  {
    reveal f();
  }
}
