
// GhostITECompilation.dfy

function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1)
  else
    F(x - 1, 60) + 13
}

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
}

function G(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    var z := x + x;
    var a, b, c := 100, if x < z then G(x, y - 1) else G(x, y - 1), 200;
    assert a + b + c == G(x, y - 1) + 300;
    b
  else
    G(x - 1, 60) + 13
}

function H(x: int, ghost y: nat): int
{
  if y == 0 then
    x
  else
    H(x, y - 1)
}

function J(x: int): int
{
  if true then
    x
  else
    J(x)
}


method Main()
{
  print F(5, 3), "\n";
  print G(5, 3), "\n";
  print H(65, 3), "\n";
}
