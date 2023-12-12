
// Bug67.dfy

method Main()
{
  assert D([10, 20]) == D([10, 20]);
  print D([10, 20]) == D([10, 20]);
}

datatype d = D(m: seq<int>)
