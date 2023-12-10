
// COST-verif-comp-2011-3-TwoDuplicates.dfy

ghost predicate IsDuplicate(a: array<int>, p: int)
  reads a
{
  IsPrefixDuplicate(a, a.Length, p)
}

ghost predicate IsPrefixDuplicate(a: array<int>, k: int, p: int)
  requires 0 <= k <= a.Length
  reads a
{
  exists i, j :: 
    0 <= i < j < k &&
    a[i] == a[j] == p
}

method Search(a: array<int>) returns (p: int, q: int)
  requires 4 <= a.Length
  requires exists p, q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < a.Length - 2
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q)
{
}
