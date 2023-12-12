
// Regression3.dfy

method Main()
{
  var z := OutParametersInLetBodies();
  DoSomeFloors();
}

method OutParametersInLetBodies() returns (t: int)
{
  t := 25;
  var z := var y := 30; F(t, y);
  assert z == 55;
  print z, "\n";
}

function F(x: int, y: int): int
{
  x + y
}

method DoSomeFloors()
{
}

method P(r: real, y: int)
  requires r.Floor == y
{
  var x := r.Floor;
  print "Trunc( ", r, " ) = ", x, " (expected ", y, ")\n";
}
