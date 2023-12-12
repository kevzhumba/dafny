
// Bug113.dfy

method Main()
{
  print D(10, 20, 30, 40);
}

datatype D = D(q: int, r: int, s: int, t: int)
