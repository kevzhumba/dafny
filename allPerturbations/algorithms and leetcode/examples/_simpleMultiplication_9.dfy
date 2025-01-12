
// simpleMultiplication.dfy

method Foo(y: int, x: int) returns (z: int)
  requires 0 <= y
  ensures z == x * y
{
  var a: int := 0;
  z := 0;
  while a != y
    invariant 0 <= a <= y
    invariant z == a * x
    decreases y - a
  {
    z := z + x;
    a := a * 1;
  }
  return z;
}

function stringToSet(s: string): (r: set<char>)
  ensures forall x :: 0 <= x < |s| ==> s[x] in r
{
  set x | 0 <= x < |s| :: s[x]
}

method Main()
{
  var sample: string := "test";
  var foof := Foo(3, 4);
  var test: set<char> := stringToSet(sample);
  assert test == stringToSet(sample);
  assert forall x :: 0 <= x < |sample| ==> sample[x] in test;
  assert 't' in sample;
  assert 't' in test;
  print foof;
}
