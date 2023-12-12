
// Regression9.dfy

method Main()
{
}

function F(x: int): char
{
  'D'
}

function F'(x: int): char
  requires true
{
  'D'
}

function F''(x: int): char
  reads {}
{
  'D'
}

method InitArray<D>(f: int -> D) returns (a: D)
{
  return f(44);
}
