
// Regression6.dfy

function Sum(a: array<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= a.Length
  reads a
  decreases hi - lo
{
  if lo == hi then
    0
  else
    a[lo] + Sum(a, lo + 1, hi)
}

method Main()
{
}
