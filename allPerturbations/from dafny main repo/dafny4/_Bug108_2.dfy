
// Bug108.dfy

method Main()
{
  var A := map[0 := 1];
  var B := map x | x in set y | y in A :: A[x];
  print A, "\n";
}
