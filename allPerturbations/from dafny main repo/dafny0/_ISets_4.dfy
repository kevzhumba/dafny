
// ISets.dfy

ghost method M()
{
}

ghost method m1()
{
  var s1: iset<int> := iset{};
  var s2 := iset{1, 2, 3};
  assert s2 == iset{1, 1, 2, 3, 3, 3, 3};
  var s3, s4 := iset{1, 2}, iset{1, 4};
  assert s2 + s4 == iset{1, 2, 3, 4};
  assert s2 * s3 == iset{1, 2} && s2 * s4 == iset{1};
  assert s2 - s3 == iset{3};
  assert (iset x | x in s2 :: x + 1) == iset{2, 3, 4};
  assert 17 in iset x: int | true :: x;
  assert (imap x: int | true :: x + 1)[14] == 15;
}
