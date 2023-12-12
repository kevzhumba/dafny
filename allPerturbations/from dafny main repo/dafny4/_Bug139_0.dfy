
// Bug139.dfy

method R(xs: List)
{
  var a: int;
  var b: int;
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(a, Nil()) =>
  case {:split false} Cons(x, Cons(b, tail)) =>
}

ghost function F(xs: List): int
{
  var a := 4;
  var b := 7;
  match xs
  case Nil =>
    0
  case Cons(a, Nil()) =>
    1
  case Cons(x, Cons(b, tail)) =>
    2
}

datatype List = Nil | Cons(int, List)
