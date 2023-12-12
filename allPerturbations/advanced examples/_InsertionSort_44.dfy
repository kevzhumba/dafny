
// InsertionSort.dfy

predicate sorted(a: array<int>, start: int, end: int)
  requires a != null
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall j, k :: 
    start <= j < k < end ==>
      a[j] <= a[k]
}

method InsertionSort(a: array<int>)
  requires a != null && a.Length > 1
  modifies a
  ensures sorted(a, 0, a.Length)
{
}

method Main()
{
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 2, 5, 1, 8;
  InsertionSort(a);
  print a[..];
}
