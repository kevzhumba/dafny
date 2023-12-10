
// CachedContainer.dfy


abstract module M0 {
  class {:autocontracts} Container<T(==)> {
    ghost var Contents: set<T>

    ghost predicate Valid()
    {
      Valid'()
    }

    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr

    constructor ()
      ensures Contents == {}

    method Add(t: T)
      ensures Contents == old(Contents) + {t}

    method Remove(t: T)
      ensures Contents == old(Contents) - {t}

    method Contains(t: T) returns (b: bool)
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
  }
}

abstract module M1 refines M0 {
  class Container<T(==)> ... {
    constructor  ...
    {
      Contents := {};
      Repr := {this};
      new;
      label CheckPost:
      assume Valid'();
    }

    method Add ...
    {
      Contents := Contents + {t};
      label CheckPost:
      assume Valid'();
    }

    method Remove ...
    {
      Contents := Contents + {t};
      label CheckPost:
      assume Valid'();
    }

    method Contains ...
    {
      b :| assume b <==> t in Contents;
    }
  }
}

abstract module M2 refines M1 {
  class Container<T(==)> ... {
    var elems: seq<T>

    ghost predicate Valid' ...
    {
      Contents == (set x | x in elems) &&
      (forall i, j :: 
        0 <= i < j < |elems| ==>
          elems[i] != elems[j]) &&
      Valid''()
    }

    ghost predicate {:autocontracts false} Valid''()
      reads this, Repr

    method FindIndex(t: T) returns (j: nat)
      ensures j <= |elems|
      ensures if j < |elems| then elems[j] == t else t !in elems
    {
      j := 0;
      while j < |elems|
        invariant j <= |elems|
        invariant forall i :: 0 <= i < j ==> elems[i] != t
      {
        if elems[j] == t {
          return;
        }
        j := j + 1;
      }
    }

    constructor  ...
    {
      elems := [];
      new;
      label CheckPost:
      assume Valid''();
      assert ...;
    }

    method Add ...
    {
      var j := FindIndex(t);
      if j == |elems| {
        elems := elems + [t];
      }
      ...;
      label CheckPost:
      assume Valid''();
      assert ...;
    }

    method Remove ...
    {
      var j := FindIndex(t);
      if j < |elems| {
        elems := elems[..j] + elems[j + 1..];
      }
      ...;
      label CheckPost:
      assume Valid''();
      assert ...;
    }

    method Contains ...
    {
      var j := FindIndex(t);
      b := j < |elems|;
    }
  }
}

module M3 refines M2 {
  datatype Cache<T> = None | Some(index: nat, value: T)

  class Container<T(==)> ... {
    var cache: Cache<T>

    ghost predicate Valid'' ...
    {
      cache.Some? ==>
        cache.index < |elems| &&
        elems[cache.index] == cache.value
    }

    constructor  ...
    {
      cache := None;
      new;
      ...;
      assert ...;
    }

    method FindIndex ...
    {
      if cache.Some? && cache.value == t {
        return cache.index;
      }
    }

    method Add ...
    {
      ...;
      assert ...;
    }

    method Remove ...
    {
      ...;
      if ... {
        if cache.Some? {
          if cache.index == j {
            cache := None;
          } else if j < cache.index {
            cache := cache.(index := cache.index - 1);
          }
        }
      }
      ...;
      assert ...;
    }
  }
}

abstract module Client {
  method Test()
  {
    var c := new M.Container();
    c.Add(56);
    c.Add(12);
    var b := c.Contains(17);
    assert !b;
    print b, " ";
    b := c.Contains(12);
    assert b;
    print b, " ";
    c.Remove(12);
    b := c.Contains(12);
    assert !b;
    print b, " ";
    assert c.Contents == {56};
    b := c.Contains(56);
    assert b;
    print b, "\n";
  }

  import M : M0
}

module CachedClient refines Client {
  method Main()
  {
    Test();
  }

  import M = M3
}
