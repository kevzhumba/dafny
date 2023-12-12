
// McCarthy91.dfy

method Main()
{
}

method M(n: int) returns (r: int)
  ensures r == if n <= 100 then 91 else n - 10
  decreases 100 - n
{
  if n <= 100 {
    r := M(n + 11);
    r := M(r);
  } else {
    r := n - 10;
  }
}

function mc91(n: int): int
  ensures n <= 100 ==> mc91(n) == 91
  decreases 100 - n
{
  if n <= 100 then
    mc91(mc91(n + 11))
  else
    n - 10
}

function iter(e: nat, f: int -> int, n: int): int
{
  if e == 0 then
    n
  else
    iter(e - 1, f, f(n))
}

method Mc91(n0: int) returns (r: int)
  ensures r == mc91(n0)
{
  var e, n := 1, n0;
  while e > 0
    invariant iter(e, mc91, n) == mc91(n0)
    decreases 100 - n + 10 * e, e
  {
    if n <= 100 {
      e, n := e + 1, n + 11;
    } else {
      e, n := e - 1, n - 10;
    }
  }
  return n;
}
