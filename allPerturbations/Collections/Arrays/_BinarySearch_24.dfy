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
  }

  import opened Wrappers

  import opened Relations
}
