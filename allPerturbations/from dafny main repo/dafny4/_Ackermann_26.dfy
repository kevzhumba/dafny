
// Ackermann.dfy

method Main()
{
  print "Ack(3, 4) = ", Ack(3, 4), "\n";
}

function Ack(m: nat, n: nat): nat
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

lemma AckermannIsMonotonic(m: nat, n: nat, m': nat, n': nat)
  requires m <= m' && n <= n'
  ensures Ack(m, n) <= Ack(m', n')
{
  MonotonicN(m, n, n');
  MonotonicM(m, n, m');
}

lemma MonotonicN(m: nat, n: nat, n': nat)
  requires n <= n'
  ensures Ack(m, n) <= Ack(m, n')
{
}

ghost function CurriedAckermann(m: int, n: int): int
{
  A(m)(n)
}

ghost function A(m: int): int -> int
{
  if m <= 0 then
    n => n + 1
  else
    n => Iter(A(m - 1), n)
}

ghost function Iter(f: int -> int, n: int): int
  decreases n
{
  if n <= 0 then
    f(1)
  else
    f(Iter(f, n - 1))
}

lemma CurriedIsTheSame(m: nat, n: nat)
  ensures CurriedAckermann(m, n) == Ack(m, n)
{
  if m == 0 {
  } else if n == 0 {
    assert CurriedAckermann(m, n) == Iter(A(m - 1), 0);
  } else {
    assert A(m)(n) == A(m - 1)(Iter(A(m - 1), n - 1));
  }
}

lemma MonotonicM(m: nat, n: nat, m': nat)
  requires m <= m'
  ensures Ack(m, n) <= Ack(m', n)
{
  CurriedIsTheSame(m, n);
  CurriedIsTheSame(m', n);
  ABelow(m, m');
}

ghost predicate FunctionBelow(f: int -> int, g: int -> int)
{
  forall n :: 
    f(n) <= g(n)
}

ghost predicate FunctionMonotonic(f: int -> int)
{
  forall n, n' :: 
    n <= n' ==>
      f(n) <= f(n')
}

ghost predicate Expanding(f: int -> int)
{
  forall n :: 
    n < f(n)
}

lemma IterIsMonotonicN(f: int -> int, n: int, n': int)
  requires Expanding(f) && FunctionMonotonic(f) && n <= n'
  ensures Iter(f, n) <= Iter(f, n')
{
}

lemma IterIsMonotonicF(f: int -> int, g: int -> int, n: int)
  requires FunctionMonotonic(f) && FunctionBelow(f, g)
  ensures Iter(f, n) <= Iter(g, n)
{
}

lemma IterExpanding(f: int -> int, n: int)
  requires Expanding(f)
  ensures n < Iter(f, n)
{
}

lemma AExp(m: int)
  ensures Expanding(A(m))
{
}

lemma Am(m: int)
  ensures FunctionMonotonic(A(m))
{
  if m <= 0 {
  } else {
    AExp(m - 1);
    forall n, n' | n <= n' {
      IterIsMonotonicN(A(m - 1), n, n');
    }
  }
}

lemma ABelow(m: int, m': int)
  requires m <= m'
  ensures FunctionBelow(A(m), A(m'))
{
  if m' <= 0 {
  } else if m <= 0 {
    forall n | true {
      calc {
        A(m)(n);
      ==
        n + 1;
      <=
        {
          AExp(m' - 1);
          IterExpanding(A(m' - 1), n);
        }
        Iter(A(m' - 1), n);
      ==
        A(m')(n);
      }
    }
  } else {
    forall n | true {
      calc {
        A(m)(n);
      ==
        Iter(A(m - 1), n);
      <=
        {
          Am(m - 1);
          ABelow(m - 1, m' - 1);
          IterIsMonotonicF(A(m - 1), A(m' - 1), n);
        }
        Iter(A(m' - 1), n);
      ==
        A(m')(n);
      }
    }
  }
}
