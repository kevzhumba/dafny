
// Bug120.dfy

ghost function G(n: nat): nat
{
  if n == 0 then
    5
  else
    G(n - 1)
}

method Test()
{
}
