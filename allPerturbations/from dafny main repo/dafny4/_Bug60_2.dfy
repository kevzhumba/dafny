
// Bug60.dfy

method Main()
{
  var s := {2, 3};
  var m := map[2 := 20, 3 := 30];
  print (s, m), "\n";
  print set s | s in m, "\n";
  print forall x :: x in map[1 := 10, 2 := 20] ==> x > 0, "\n";
}
