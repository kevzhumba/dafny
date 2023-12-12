
// git-issue74.dfy

function {:opaque} f(x: int): int
{
  x
}

lemma L()
  ensures forall x: int :: f(x) == x
{
  assert forall x: int :: f(x) == x;
}
