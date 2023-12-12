
// TuringFactorial.dfy

ghost function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n
  ensures u == Factorial(n)
{
  var r := 1;
  u := 1;
  while r < n
    invariant r <= n
    invariant u == Factorial(r)
  {
    r := r + 1;
  }
}
