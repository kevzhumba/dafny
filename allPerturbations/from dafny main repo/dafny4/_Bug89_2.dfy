
// Bug89.dfy

method F() returns (x: int)
  ensures x == 6
{
}

method Main()
{
  var x := F();
  print x;
}
