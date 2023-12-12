
// ImplicitTypeParamPrint.dfy

function funkyNil(l: List): List
{
  match l
  case Cons(x, y) =>
    funkyNil(y)
  case Nil =>
    l
}

method H(a: array, l: List)
{
  match l
  case {:split false} Cons(x, y) =>
    if a.Length < 0 && a[0] == x {
    }
  case {:split false} Nil =>
}

method Main()
{
  var xs := Cons(28, Cons(22, Cons(28, Cons(5, Nil))));
  var a := new [] [60, 60];
  var nil := funkyNil(xs);
  H(a, xs);
  print nil, "\n";
  print nonExtendedPrintExpr(xs), "\n";
}

function nonExtendedPrintExpr(l: List): int
{
  25 + match l case Cons(x, y) => 10 case Nil => 11
}

datatype List<T> = Nil | Cons(car: T, cdr: List)
