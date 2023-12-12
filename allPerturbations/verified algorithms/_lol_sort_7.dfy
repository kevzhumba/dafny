
// lol_sort.dfy

predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..])[i := old(a[j])][j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
{
  a[i], a[j] := a[j], a[i];
}

predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: 
    a[i] <= a[j]
}

method lol_sort(a: array<int>)
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
{
  for i := 0 to a.Length
    invariant valid_permut(a[..], old(a[..]))
    invariant sorted(a[..i])
  {
    for j := 0 to a.Length
      invariant valid_permut(a[..], old(a[..]))
      invariant j < i ==> forall k | 0 <= k < j :: a[k] <= a[i]
      invariant j < i ==> sorted(a[..i])
      invariant j >= i ==> sorted(a[..i + 1])
    {
      if a[i] != a[j] {
        swap(a, i, j);
      }
    }
  }
}

method Main()
{
  var a := new int[] [3, 1, 4, 1, 5, 9, 2, 6];
  lol_sort(a);
  print a[..];
  expect a[..] == [1, 1, 2, 3, 4, 5, 6, 9];
  var empty := new int[] [];
  lol_sort(empty);
  assert empty[..] == [];
}
