
// Bug107.dfy

method Main()
{
  var f := Inc;
}

function Inc(x: int): int
{
  x + 2
}
