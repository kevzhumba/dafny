
// GhostPrint.dfy

method M()
{
  ghost var h := var ta := F(); 5;
  var j := ghost var tb := F(); 5;
}

ghost function F(): int
{
  5
}
