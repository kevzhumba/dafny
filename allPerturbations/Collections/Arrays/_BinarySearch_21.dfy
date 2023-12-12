include "../../Wrappers.dfy"
include "../../Relations.dfy"
// BinarySearch.dfy


module BinarySearch {
  method BinarySearch<T>(a: array<T>, key: T, less: (T, T) -> bool)
      returns (r: Option<nat>)
    requires SortedBy(a[..], (x, y) => less(x, y) || x == y)
    requires StrictTotalOrdering(less)
    ensures r.Some? ==> r.value < a.Length && a[r.value] == key
    ensures r.None? ==> key !in a[..]
  {
    var lo, hi: nat := 0, a.Length;
    while lo < hi
      invariant 0 <= lo <= hi <= a.Length
      invariant key !in a[..lo] && key !in a[hi..]
      invariant a[..] == old(a[..])
    {
      var mid := (lo + hi) / 2;
    }
    return None;
  }

  import opened Wrappers

  import opened Relations
}
