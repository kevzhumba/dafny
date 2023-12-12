
// SimpleInduction.dfy

ghost function Fib(n: nat): nat
  decreases n
{
  if n < 2 then
    n
  else
    Fib(n - 2) + Fib(n - 1)
}

lemma FibLemma(n: nat)
  ensures Fib(n) % 2 == 0 <==> n % 3 == 0
  decreases n
{
  if n < 2 {
  } else {
    FibLemma(n - 2);
    FibLemma(n - 1);
  }
}

lemma FibLemma_Alternative(n: nat)
  ensures Fib(n) % 2 == 0 <==> n % 3 == 0
{
  forall k | 0 <= k < n {
    FibLemma_Alternative(k);
  }
}

lemma FibLemma_All()
  ensures forall n :: 0 <= n ==> (Fib(n) % 2 == 0 <==> n % 3 == 0)
{
}

ghost function Append<T>(xs: List<T>, ys: List<T>): List<T>
  decreases xs
{
  match xs
  case Nil =>
    ys
  case Cons(x, rest) =>
    Cons(x, Append(rest, ys))
}

lemma {:induction false} AppendIsAssociative(xs: List, ys: List, zs: List)
  ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
  decreases xs
{
  match xs {
    case {:split false} Nil =>
    case {:split false} Cons(x, rest) =>
      AppendIsAssociative(rest, ys, zs);
  }
}

lemma AppendIsAssociative_Auto(xs: List, ys: List, zs: List)
  ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
