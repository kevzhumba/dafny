
// Bug89.dfy

method F() returns (x: int)
  ensures x == 6
{
  x := 4;
  x := var y := 1; y + x;
}

method Main()
{
  var x := F();
  print x;
}
