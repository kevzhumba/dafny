
// git-issue88.dfy

method M2()
{
  var g: Grid := new int[9, 9];
  g[0, 0] := 1;
}

method M1()
{
  var g: Line := new int[9];
  g[0] := 1;
}

method Main()
{
}

type Grid = array2<int>

type Line = array<int>
