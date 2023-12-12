
// Bug138.dfy

method R(xs: List)
{
  match xs
  case {:split false} Nil() =>
  case {:split false} Cons(x, Nil()) =>
  case {:split false} Cons(x, Cons(y, tail)) =>
}

ghost function F(xs: List): int
{
  match xs
  case Nil() =>
    0
  case Cons(x, Nil()) =>
    1
  case Cons(x, Cons(y, tail)) =>
    2
}

datatype List = Nil | Cons(int, List)
