
// Classics.dfy

ghost function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n)
{
  u := 1;
  var r := 0;
  while r < n
    invariant 0 <= r <= n
    invariant u == Factorial(r)
  {
    var v := u;
    var s := 1;
    while s <= r
      invariant 1 <= s <= r + 1
      invariant u == s * Factorial(r)
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N
  requires 0 <= f < N
  modifies A
  ensures forall p, q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
  var m, n := 0, N - 1;
}
