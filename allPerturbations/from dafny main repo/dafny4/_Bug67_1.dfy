
// Bug67.dfy

method Main()
{
  print [10, 20] == [10, 20], "\n";
  print D([10, 20]) == D([10, 20]);
}

datatype d = D(m: seq<int>)
