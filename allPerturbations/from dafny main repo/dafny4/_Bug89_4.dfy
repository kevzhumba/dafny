
// Bug89.dfy

method F() returns (x: int)
  ensures x == 6
{
  x := 5;
}

method Main()
{
  var x := F();
  print x;
}
