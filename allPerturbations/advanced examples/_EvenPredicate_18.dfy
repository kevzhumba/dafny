
// EvenPredicate.dfy

function IsEven(a: int): bool
  requires a >= 0
{
  if a == 0 then
    true
  else if a == 1 then
    false
  else
    IsEven(a - 2)
}

lemma EvenSquare(a: int)
  requires a >= 0
  ensures IsEven(a) ==> IsEven(a * a)
{
}

lemma EvenDouble(a: int)
  requires a >= 0
  ensures IsEven(a + a)
{
  if a >= 2 {
    EvenDouble(a - 2);
  }
}

lemma {:induction x} EvenPlus(x: int, y: int)
  requires x >= 0
  requires y >= 0
  requires IsEven(x)
  requires IsEven(y)
  ensures IsEven(x + y)
{
  if x >= 2 {
    EvenPlus(x - 2, y);
  }
}
