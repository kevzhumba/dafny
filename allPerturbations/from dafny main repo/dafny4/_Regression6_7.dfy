
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
  var a := new int[100];
  var b := new int[1000];
  assert a != b;
  var s := Sum(a, 0, a.Length);
  assert s == Sum(a, 0, a.Length);
  b[17] := 1028;
  assert s == Sum(a, 0, a.Length);
}
