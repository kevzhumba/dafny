
// Refinement.dfy

method Main()
{
}

abstract module Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
}

abstract module Mod {
  method m()
  {
    assert 6 <= A.addSome(5);
    print "Test\n";
  }

  import A : Interface
}

module Implementation refines Interface {
  function addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}

module Mod2 refines Mod {

  import A = Implementation
}
