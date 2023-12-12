
// KatzManna.dfy

method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x - 10 else 91
{
  var y1 := x;
  var y2 := 1;
  while true
    invariant proveFunctionalPostcondition ==> 100 < x ==> y1 == x
    invariant proveFunctionalPostcondition ==> x <= 100 < y1 && y2 == 1 ==> y1 == 101
    invariant (y1 <= 111 && y2 >= 1) || (y1 == x && y2 == 1)
    decreases -2 * y1 + 21 * y2 + 2 * if x < 111 then 111 else x
  {
    if y1 > 100 {
      if y2 == 1 {
        break;
      } else {
        y1 := y1 - 10;
        y2 := y2 - 1;
      }
    } else {
      y1 := y1 + 11;
      y2 := y2 + 1;
    }
  }
  z := y1 - 10;
}

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2
{
  var y1 := x1;
  var y2 := x2;
  while y1 != y2
    invariant 1 <= y1 && 1 <= y2
    decreases y1 + y2
  {
    while y1 > y2
      invariant 1 <= y1 && 1 <= y2
    {
      y1 := y1 - y2;
    }
    while y2 > y1
      invariant 1 <= y1 && 1 <= y2
    {
      y2 := y2 - y1;
    }
  }
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M
  requires M == X.Length0 && M == X.Length1
  modifies X
{
}