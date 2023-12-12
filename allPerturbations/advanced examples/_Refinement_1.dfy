
// Refinement.dfy

method Main()
{
  Mod2.m();
}

abstract module Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
}

abstract module Mod {
  method m()
  {
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
