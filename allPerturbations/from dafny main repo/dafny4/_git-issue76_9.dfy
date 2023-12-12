
// git-issue76.dfy

method Main()
{
  M0();
  M1();
  EqualityOfStrings0();
  EqualityOfStrings1();
}

method M0()
{
  assert {"x", "y", "z"} - {"y"} == {"x", "z"};
}

method M1()
{
  var n :| ("R", n) in {("R", 2), ("P", 1)};
  assert n == 2;
  print n, "\n";
}

method EqualityOfStrings0()
{
}

method EqualityOfStrings1()
{
  assert "a" + "b" == "ab";
}

method M2()
{
  assert !([0, 0] in {[0, 2], [1, 2]});
}

method M3()
{
  assert [0, 0] !in {[0, 2], [1, 2]};
}
