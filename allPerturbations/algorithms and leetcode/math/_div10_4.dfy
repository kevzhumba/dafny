
// div10.dfy

method divu10(n: bv16) returns (r: bv16)
  ensures r == n / 10
{
  var q: bv16;
  q := n >> 1 + n >> 2;
  q := q * (q >> 4);
  q := q + q >> 8;
  q := q >> 3;
  r := n - (q << 2 + q) << 1;
  return q + if r > 9 then 1 else 0;
}
