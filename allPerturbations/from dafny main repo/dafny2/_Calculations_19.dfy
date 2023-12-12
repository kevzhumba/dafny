
// Calculations.dfy

ghost function length(l: List): nat
{
  match l
  case Nil =>
    0
  case Cons(x, xs) =>
    1 + length(xs)
}

ghost function concat(l: List, ys: List): List
{
  match l
  case Nil =>
    ys
  case Cons(x, xs) =>
    Cons(x, concat(xs, ys))
}

ghost function reverse(l: List): List
{
  match l
  case Nil =>
    Nil
  case Cons(x, xs) =>
    concat(reverse(xs), Cons(x, Nil))
}

ghost function revacc(l: List, acc: List): List
{
  match l
  case Nil =>
    acc
  case Cons(x, xs) =>
    revacc(xs, Cons(x, acc))
}

ghost function qreverse(l: List): List
{
  revacc(l, Nil)
}

lemma Lemma_ConcatNil(xs: List)
  ensures concat(xs, Nil) == xs
{
}

lemma Lemma_RevCatCommute(xs: List)
  ensures forall ys, zs :: revacc(xs, concat(ys, zs)) == concat(revacc(xs, ys), zs)
{
}

lemma Theorem_QReverseIsCorrect_Calc(l: List)
  ensures qreverse(l) == reverse(l)
{
  calc {
    qreverse(l);
    revacc(l, Nil);
    {
      Lemma_Revacc_calc(l, Nil);
    }
    concat(reverse(l), Nil);
    {
      Lemma_ConcatNil(reverse(l));
    }
    reverse(l);
  }
}

lemma Lemma_Revacc_calc(xs: List, ys: List)
  ensures revacc(xs, ys) == concat(reverse(xs), ys)
{
  match xs {
    case {:split false} Nil =>
    case {:split false} Cons(x, xrest) =>
      calc {
        concat(reverse(xs), ys);
        concat(concat(reverse(xrest), Cons(x, Nil)), ys);
        concat(revacc(xrest, Cons(x, Nil)), ys);
        {
          Lemma_RevCatCommute(xrest);
        }
        revacc(xrest, concat(Cons(x, Nil), ys));
        revacc(xrest, Cons(x, ys));
        revacc(xs, ys);
      }
  }
}

lemma Theorem_QReverseIsCorrect(l: List)
  ensures qreverse(l) == reverse(l)
{
  assert qreverse(l) == revacc(l, Nil);
  Lemma_Revacc(l, Nil);
  assert revacc(l, Nil) == concat(reverse(l), Nil);
  Lemma_ConcatNil(reverse(l));
}

lemma Lemma_Revacc(xs: List, ys: List)
  ensures revacc(xs, ys) == concat(reverse(xs), ys)
{
  match xs {
    case {:split false} Nil =>
    case {:split false} Cons(x, xrest) =>
      assert revacc(xs, ys) == revacc(xrest, Cons(x, ys));
      assert concat(reverse(xs), ys) == concat(concat(reverse(xrest), Cons(x, Nil)), ys) == concat(revacc(xrest, Cons(x, Nil)), ys);
      Lemma_RevCatCommute(xrest);
      assert concat(revacc(xrest, Cons(x, Nil)), ys) == revacc(xrest, concat(Cons(x, Nil), ys));
      assert forall g, gs :: concat(Cons(g, Nil), gs) == Cons(g, gs);
      assert revacc(xrest, concat(Cons(x, Nil), ys)) == revacc(xrest, Cons(x, ys));
  }
}

ghost function Fib(n: nat): nat
{
  if n < 2 then
    n
  else
    Fib(n - 2) + Fib(n - 1)
}

lemma Lemma_Fib()
  ensures Fib(5) < 6
{
  calc {
    Fib(5);
    Fib(4) + Fib(3);
  <
    calc {
      Fib(2);
      Fib(0) + Fib(1);
      0 + 1;
      1;
    }
    6;
  }
}

lemma Lemma_Concat_Length(xs: List, ys: List)
  ensures length(concat(xs, ys)) == length(xs) + length(ys)
{
}

lemma Lemma_Reverse_Length(xs: List)
  ensures length(xs) == length(reverse(xs))
{
}

lemma Window(xs: List, ys: List)
  ensures length(xs) == length(ys) ==> length(reverse(xs)) == length(reverse(ys))
{
  calc {
    length(xs) == length(ys) ==>
      length(reverse(xs)) == length(reverse(ys));
    {
      if length(xs) == length(ys) {
        calc {
          length(reverse(xs));
          {
            Lemma_Reverse_Length(xs);
          }
          length(xs);
          length(ys);
          {
            Lemma_Reverse_Length(ys);
          }
          length(reverse(ys));
        }
      }
    }
    length(xs) == length(ys) ==>
      length(reverse(xs)) == length(reverse(xs));
    true;
  }
}

ghost function ith<a>(xs: List, i: nat): a
  requires i < length(xs)
{
  match xs
  case Cons(x, xrest) =>
    if i == 0 then
      x
    else
      ith(xrest, i - 1)
}

lemma lemma_zero_length(xs: List)
  ensures length(xs) == 0 <==> xs.Nil?
{
}

lemma lemma_extensionality(xs: List, ys: List)
  requires length(xs) == length(ys)
  requires forall i: nat | i < length(xs) :: ith(xs, i) == ith(ys, i)
  ensures xs == ys
{
  match xs {
    case {:split false} Nil =>
      calc {
        true;
        length(xs) == length(ys);
        0 == length(ys);
        {
          lemma_zero_length(ys);
        }
        Nil == ys;
        xs == ys;
      }
    case {:split false} Cons(x, xrest) =>
      match ys {
        case {:split false} Cons(y, yrest) =>
          calc {
            xs;
            Cons(x, xrest);
            calc {
              x;
              ith(xs, 0);
              ith(ys, 0);
              y;
            }
            Cons(y, xrest);
            {
              forall j: nat | j < length(xrest) {
                calc {
                  ith(xrest, j);
                  ith(xs, j + 1);
                  ith(ys, j + 1);
                  ith(yrest, j);
                }
              }
              lemma_extensionality(xrest, yrest);
            }
            Cons(y, yrest);
            ys;
          }
      }
  }
}

datatype List<T> = Nil | Cons(T, List)
