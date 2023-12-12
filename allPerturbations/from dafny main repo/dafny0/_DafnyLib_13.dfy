
// DafnyLib.dfy


module AmbiguousNestedModule {
}

module Library {
  method EntryPoint()
  {
    print "hello from the library\n";
    OpaqueFunctions.IsFive();
    AutoGhostRegression.Q();
  }

  import OpaqueFunctions

  import AutoGhostRegression

  import ExternCode

  module AmbiguousNestedModule {
    method EntryPoint()
    {
      print "hello from a nested module\n";
    }
  }
}

module {:extern "ExternCode"} ExternCode {
  method {:extern} C()
}

module OpaqueFunctions {
  ghost function {:opaque} Five(): int
  {
    5
  }

  lemma IsFive()
    ensures Five() == 5
  {
    reveal Five();
  }
}

module AutoGhostRegression {
  method P() returns (a: int, ghost b: int)
  {
    a, b := 9, 11;
  }

  method NeedsNonGhost(u: int)
  {
  }

  method Q()
  {
    var u, v := P();
    NeedsNonGhost(u);
  }
}
