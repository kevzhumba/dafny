
// Bug67.dfy

method Main()
{
  assert D([10, 20]) == D([10, 20]);
  print [10, 20] == [10, 20], "\n";
}

datatype d = D(m: seq<int>)
