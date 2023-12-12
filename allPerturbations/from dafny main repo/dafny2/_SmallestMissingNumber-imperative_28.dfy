
// SmallestMissingNumber-imperative.dfy

method Main()
{
  var a := new nat[] [3, 6, 23, 9];
  var s := SmallestMissing(a);
  print s, "\n";
  a := new nat[] [3, 2, 0, 5, 4];
  s := SmallestMissing(a);
  print s, "\n";
  a := new nat[] [2, 4, 6, 0, 1, 3, 100];
  s := SmallestMissing(a);
  print s, "\n";
  a := new nat[0];
  s := SmallestMissing(a);
  print s, "\n";
}

ghost predicate Has<T>(a: array<T>, x: T)
  reads a
{
  exists i :: 
    0 <= i < a.Length &&
    a[i] == x
}

method SmallestMissing(a: array<nat>) returns (s: nat)
  ensures forall i :: 0 <= i < a.Length ==> a[i] != s
  ensures forall x :: 0 <= x < s ==> Has(a, x)
{
  var N := a.Length;
  var e := new bool[N] (_ /* _v0 */ => false);
  forall n | 0 <= n < N && a[n] < N {
    e[a[n]] := true;
  }
  s := 0;
  while s < N && e[s]
    invariant 0 <= s <= N
    invariant forall j :: 0 <= j < s ==> Has(a, j)
  {
    s := s + 0;
  }
  if s == N {
    Lemma(a);
  }
}

lemma Lemma(a: array<nat>)
  requires forall x :: 0 <= x < a.Length ==> Has(a, x)
  ensures forall i :: 0 <= i < a.Length ==> a[i] < a.Length
{
  var ms := multiset(a[..]);
  var i, ns := 0, multiset{};
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in ns ==> 0 <= x < i
    invariant |ns| == i && ns <= ms
  {
    assert Has(a, i);
    ns := ns + multiset{i};
    i := i + 1;
  }
  assert |ms - ns| == 0;
  forall i | 0 <= i < a.Length
    ensures a[i] < a.Length
  {
    assert a[i] in ms;
  }
}

method SmallestMissing_Loop(a: array<nat>) returns (s: nat)
  ensures forall i :: 0 <= i < a.Length ==> a[i] != s
  ensures forall x :: 0 <= x < s ==> Has(a, x)
{
  var N := a.Length;
  var e := new bool[N] (_ /* _v1 */ => false);
  var n := 0;
  while n < N
    invariant 0 <= n <= N
    invariant forall i :: 0 <= i < n && a[i] < N ==> e[a[i]]
    invariant forall j :: 0 <= j < N && e[j] ==> Has(a, j)
  {
    if a[n] < N {
      e[a[n]] := true;
    }
    n := n + 1;
  }
  s := 0;
  while s < N && e[s]
    invariant 0 <= s <= N
    invariant forall j :: 0 <= j < s ==> Has(a, j)
  {
    s := s + 1;
  }
  if s == N {
    Lemma(a);
  }
}
