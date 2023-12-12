
// Regression3.dfy

method Main()
{
  var z := OutParametersInLetBodies();
  DoSomeFloors();
}

method OutParametersInLetBodies() returns (t: int)
{
  t := 24;
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
  P(-3.0, -3);
  P(-2.8, -3);
  P(-2.2, -3);
  P(-0.1, -1);
  P(0.0, 0);
  P(0.1, 0);
  P(2.2, 2);
  P(2.8, 2);
  P(3.0, 3);
}

method P(r: real, y: int)
  requires r.Floor == y
{
  var x := r.Floor;
  print "Trunc( ", r, " ) = ", x, " (expected ", y, ")\n";
}
