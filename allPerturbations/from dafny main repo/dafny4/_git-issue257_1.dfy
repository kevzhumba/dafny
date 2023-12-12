
// git-issue257.dfy

method Test0()
{
  var c := new M.C();
  var g: M.T := c;
  assert g.f() == 0;
}

method Test1()
{
  var c := new M.C();
  var g: M.T := c;
  assert c.f() == 0;
}

method Test2()
{
  var c := new M.C();
  assert c.f() == 0;
}

method Test3()
{
  var c: M.C := new M.C();
  var g: M.T := c;
  assert c.f() == 0;
}

method Test4(c: M.C, g: M.T)
  requires c == g
{
  assert c.f() == 0;
  assert g.f() == 0;
}

module M {
  trait T {
    ghost function f(): nat
  }

  class C extends T {
    constructor ()
    {
    }

    ghost function f(): nat
    {
      0
    }
  }
}
