
// Regression9.dfy

method Main()
{
  var f := F;
  var f' := F';
  var f'' := F'';
  var c := InitArray(F);
  var d := InitArray(F');
  var e := InitArray(F'');
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
