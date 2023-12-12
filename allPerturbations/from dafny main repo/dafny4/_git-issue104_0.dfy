
// git-issue104.dfy

predicate bug(a: array<int>)
  reads a
{
  forall i, j | 0 <= i <= j < a.Length :: 
    a[i] <= a[j]
}

method Main()
{
}
