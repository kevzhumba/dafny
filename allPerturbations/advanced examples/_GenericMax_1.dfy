
// GenericMax.dfy

method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  requires a != null && a.Length > 0
  requires forall x, y :: cmp.requires(x, y)
  requires forall x, y :: cmp(x, y) || cmp(y, x)
  requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z)
  ensures forall x :: 0 <= x < a.Length ==> cmp(a[x], max)
{
  max := a[0];
  var i := -1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> cmp(a[x], max)
  {
    if !cmp(a[i], max) {
      max := a[i];
    }
    i := i + 1;
  }
}
