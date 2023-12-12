
// ISets.dfy

ghost method M()
{
  ghost var s := iset{2};
  if 2 in s {
  } else {
    assert false;
  }
  if 3 !in s {
  } else {
    assert false;
  }
  if s == iset{2} {
  } else {
    assert false;
  }
}

ghost method m1()
{
}
