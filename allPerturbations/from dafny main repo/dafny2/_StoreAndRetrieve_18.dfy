
// StoreAndRetrieve.dfy


abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>

    ghost predicate Valid()
    {
      Valid'()
    }

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr

    constructor Init()
      ensures Contents == {}

    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}

    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
  }
}

abstract module A refines AbstractInterface {
  class StoreAndRetrieve<Thing(==)> ... {
    constructor Init ...
    {
      Contents := {};
      Repr := {this};
      new;
      assume Valid'();
    }

    method Store ...
    {
      Contents := Contents + {t};
      assume Valid'();
    }

    method Retrieve ...
    {
      var k :| assume k in Contents && matchCriterion(k);
      thing := k;
    }
  }
}

abstract module B refines A {
  class StoreAndRetrieve<Thing(==)> ... {
    var arr: seq<Thing>

    ghost predicate Valid' ...
    {
      Contents == set x | x in arr
    }

    constructor Init ...
    {
      arr := [];
      new;
      assert ...;
    }

    method Store ...
    {
    }

    method Retrieve ...
    {
      var i := 0;
      while i < |arr|
        invariant i < |arr|
        invariant forall j :: 0 <= j < i ==> !matchCriterion(arr[j])
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      var k := arr[i];
      ...;
      var a: seq<Thing> :| assume Contents == set x | x in a;
      arr := a;
    }
  }
}

module abC refines B {
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve ...
    {
      ...;
      var a := [thing] + arr[..i] + arr[i + 1..];
    }
  }
}

abstract module AbstractClient {
  method Test()
  {
    var s := new S.StoreAndRetrieve<real>.Init();
    s.Store(20.3);
    var fn := r => true;
    var r := s.Retrieve(fn);
    print r, "\n";
  }

  import S : AbstractInterface
}

module Client refines AbstractClient {
  method Main()
  {
    Test();
  }

  import S = abC
}
