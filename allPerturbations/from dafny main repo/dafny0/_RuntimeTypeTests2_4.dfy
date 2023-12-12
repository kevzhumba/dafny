
// RuntimeTypeTests2.dfy

predicate ItWasReal(r: real)
{
  r == 44.1985
}

method AssignSuchThat() returns (a: int, b: real)
{
  a :| a % 5 == 0 && a % 7 == 0;
  assert ItWasReal(44.1985);
  b :| ItWasReal(b);
}

method LetSuchThat() returns (x: int, y: real)
{
}
