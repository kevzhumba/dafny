
// Bug68.dfy

method M1()
{
  var m := map[{10, 20} := 33];
  assert {10, 20} in m;
  print {10, 20} in m, "\n";
}

method M1'()
{
}

method M2()
{
  var m := map[map[1 := 10, 2 := 20] := 33];
  assert map[1 := 10, 2 := 20] in m;
  print map[1 := 10, 2 := 20] in m, "\n";
}

method M2'()
{
  var m := map[map[1 := 10, 2 := 20] := 33];
  assert map[1 := 10, 2 := 20] == map[2 := 20, 1 := 10];
  assert map[2 := 20, 1 := 10] in m;
  print map[2 := 20, 1 := 10] in m, "\n";
}

method M3()
{
  var m := map[multiset{10, 20} := 33];
  assert multiset{10, 20} in m;
  print multiset{10, 20} in m, "\n";
}

method M3'()
{
  var m := map[multiset{10, 20} := 33];
  assert multiset{10, 20} == multiset{20, 10};
  assert multiset{20, 10} in m;
  print multiset{20, 10} in m, "\n";
}

method M4()
{
  var m := map[[10, 20] := 33];
  assert [10, 20] in m;
  print [10, 20] in m, "\n";
}

method Main()
{
  M1();
  M1'();
  M2();
  M2'();
  M3();
  M3'();
  M4();
}
