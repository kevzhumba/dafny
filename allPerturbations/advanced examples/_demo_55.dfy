
// demo.dfy

method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
{
  var i := 0;
  var j := a.Length;
  var k := a.Length;
  return i, k;
}
