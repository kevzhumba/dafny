
// Bug138.dfy

method R(xs: List)
{
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
