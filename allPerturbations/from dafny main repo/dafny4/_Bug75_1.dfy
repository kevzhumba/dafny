
// Bug75.dfy

ghost predicate R1(x: int, y: int)
{
  x > 0 ==>
    R2(x - 1)
}

ghost predicate R2(x: int)
{
  exists y :: 
    R1(x, y)
}

lemma L1(x: int)
{
  assert exists y :: R1(x, y);
}

lemma L2(x: int)
  requires R2(x)
{
  assume R2(x);
  assert exists y :: R1(x, y);
}

predicate Increasing(s: seq<int>, n: nat)
  requires n <= |s|
{
  n < 2 || (s[n - 2] < s[n - 1] && Increasing(s, n - 1))
}

method Extend(s: seq<int>, n: nat) returns (n': nat)
  requires n < |s|
  requires forall i :: 0 <= i < n ==> Increasing(s, i)
  ensures n <= n' <= |s|
  ensures forall j :: 0 <= j < n' ==> Increasing(s, j)
{
  if 2 <= n && s[n - 2] < s[n - 1] {
    n' := n + 1;
  } else {
    n' := n;
  }
}

ghost function pred(i: int): int
{
  i - 1
}

ghost predicate f(a: int, s: int)
{
  a <= 0 || exists s0 :: f(pred(a), s0)
}

lemma Fuel1(a: int, s: int)
{
  assert f(a, s) <==> a <= 0 || exists s0 :: f(pred(a), s0);
}
