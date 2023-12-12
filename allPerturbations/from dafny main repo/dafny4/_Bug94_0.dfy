
// Bug94.dfy

ghost function foo(): (int, int)
{
  (5, 10)
}

ghost function bar(): int
{
  var (x, y) := foo();
  x + y
}

lemma test()
{
}

function foo2(): (int, int)
{
  (5, 10)
}

method test2()
{
  var (x, y) := foo2();
}

method Main()
{
  var (x, y) := foo2();
  assert x + y == 15;
  print x + y;
}
