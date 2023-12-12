
// InductionLoop.dfy

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

lemma {:induction x} EvenPlus(x: int, y: int)
  requires x >= 0
  requires y >= 0
  requires IsEven(x)
  requires IsEven(y)
  ensures IsEven(x + y)
{
}

lemma {:induction y} EvenPlus2(x: int, y: int)
  requires x >= 0
  requires y >= 0
  requires IsEven(x)
  requires IsEven(y)
  ensures IsEven(x + y)
{
}

lemma {:induction false} EvenPlus3(x: int, y: int)
  requires x >= 0
  requires y >= 0
  requires IsEven(x)
  requires IsEven(y)
  ensures IsEven(x + y)
{
}

lemma EvenPlus4(x: int, y: int, z: int)
  requires x >= 0
  requires y >= 0
  requires IsEven(x)
  requires IsEven(y)
  requires z == x + y
  ensures IsEven(z)
{
}
