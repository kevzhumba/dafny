
// git-issue1.dfy

ghost function P(x: int): int
{
  x - 1
}

ghost function ToInt(t: T): int
  ensures ToInt(t) == t.n as int
{
  t.n as int
}

method Test(x: int)
{
  assert exists p: int :: exists t: T :: ToInt(t) > 0;
}

datatype T = T(n: int)
