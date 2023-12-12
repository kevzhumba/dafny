
// demo452.dfy

method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall i | 0 <= i < lo :: a[i] < 0
  ensures forall i | lo <= i < hi :: a[i] == 0
  ensures forall i | hi <= i < a.Length :: a[i] > 0
{
  var i := 0;
  var j := a.Length;
  var k := a.Length;
  return i, k;
}

method Main()
{
  var x := 3;
  assert x < 7;
}
