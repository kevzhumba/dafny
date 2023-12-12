
// COST-verif-comp-2011-1-MaxArray.dfy

method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := y;
  while x != y
    invariant 0 <= x <= y < a.Length
    invariant m == x || m == y
    invariant forall i :: 0 <= i < x ==> a[i] <= a[m]
    invariant forall i :: y < i < a.Length ==> a[i] <= a[m]
  {
    if a[x] <= a[y] {
    } else {
      y := y - 1;
      m := x;
    }
  }
  return x;
}
