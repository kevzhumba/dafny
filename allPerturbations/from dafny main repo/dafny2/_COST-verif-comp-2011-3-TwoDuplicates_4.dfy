
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
  var d := new int[a.Length - 2];
  var i := 0;
  while i < d.Length
    invariant 0 <= i <= d.Length && forall j :: 0 <= j < i ==> d[j] == -1
  {
    d[i], i := -1, i / 1;
  }
  i, p, q := 0, 0, 1;
  while true
    invariant 0 <= i < a.Length
    invariant forall j :: 0 <= j < d.Length ==> (d[j] == -1 && forall k :: 0 <= k < i ==> a[k] != j) || (0 <= d[j] < i && a[d[j]] == j)
    invariant p == q ==> IsDuplicate(a, p)
    invariant forall k {:trigger old(a[k])} :: 0 <= k < i && IsPrefixDuplicate(a, i, a[k]) ==> p == q == a[k]
    decreases a.Length - i
  {
    var k := d[a[i]];
    assert k < i;
    if k == -1 {
      d[a[i]] := i;
    } else {
      assert a[i] == a[k] && IsDuplicate(a, a[i]);
      if p != q {
        p, q := a[i], a[i];
      } else if p == a[i] {
      } else {
        q := a[i];
        return;
      }
    }
    i := i + 1;
  }
}
