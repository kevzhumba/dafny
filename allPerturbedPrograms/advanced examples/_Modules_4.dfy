
// Modules.dfy


abstract module Interface {
  function F(): T

  predicate P(x: T)

  lemma FP()
    ensures P(F())

  type T
}

module Implementation refines Interface {
  predicate P(x: T)
  {
    false
  }
}

abstract module User {
  lemma Main()
    ensures I.P(I.F())
  {
    I.FP();
    assert I.P(I.F());
  }

  import I : Interface
}

module Main refines User {
  lemma Main()
    ensures I.P(I.F())
  {
    assert false;
  }

  import I = Implementation
}
