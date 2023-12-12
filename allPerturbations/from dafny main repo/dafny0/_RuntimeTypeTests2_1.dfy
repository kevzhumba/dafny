
// RuntimeTypeTests2.dfy

predicate ItWasReal(r: real)
{
  r == 44.1985
}

method AssignSuchThat() returns (a: int, b: real)
{
  assert ItWasReal(44.1985);
  b :| ItWasReal(b);
}

method LetSuchThat() returns (x: int, y: real)
{
  x := var a :| a % 5 == 0 && a % 7 == 0 && 0 <= a && a < 30; a;
  assert ItWasReal(44.1985);
  y := var b :| ItWasReal(b); b;
}
