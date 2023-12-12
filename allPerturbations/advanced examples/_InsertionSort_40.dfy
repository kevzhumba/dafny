
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
  var up := 1;
  while up < a.Length
    invariant 1 <= up <= a.Length
    invariant sorted(a, 0, up)
  {
    var down := up - 1;
    var temp := a[up];
    up := up + 1;
  }
}

method Main()
{
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 2, 5, 1, 8;
  InsertionSort(a);
  print a[..];
}
