
// EWD-1062.dfy

ghost predicate Below(x: T, y: T)

lemma Reflexive(x: T)
  ensures Below(x, x)

lemma Transitive(x: T, y: T, z: T)
  ensures Below(x, y) && Below(y, z) ==> Below(x, z)

ghost function f(x: T): T

ghost function g(x: T): T

lemma Connection(x: T, y: T)
  ensures Below(f(x), y) == Below(x, g(y))

lemma Monotonic(u: T, v: T)
  requires Below(u, v)
  ensures Below(f(u), f(v)) && Below(g(u), g(v))
{
  FMonotonic(u, v);
  GMonotonic(u, v);
}

lemma FMonotonic(u: T, v: T)
  requires Below(u, v)
  ensures Below(f(u), f(v))
{
  calc {
    Below(f(u), f(v));
  ==
    {
      Reflexive(f(v));
    }
    Below(f(v), f(v)) ==>
      Below(f(u), f(v));
  ==
    {
      Connection(v, f(v));
      Connection(u, f(v));
    }
    Below(v, g(f(v))) ==>
      Below(u, g(f(v)));
  <==
    {
      Transitive(u, v, g(f(v)));
    }
    Below(u, v);
  }
}

ghost predicate Above(x: T, y: T)
{
  Below(y, x)
}

lemma AboveReflexive(x: T)
  ensures Above(x, x)
{
  Reflexive(x);
}

lemma AboveTransitive(x: T, y: T, z: T)
  ensures Above(x, y) && Above(y, z) ==> Above(x, z)
{
  Transitive(z, y, x);
}

lemma GeneralMonotonic(u: T, v: T, below: (T, T) -> bool, a: T -> T, b: T -> T)
  requires forall x :: below(x, x)
  requires forall x, y, z :: below(x, y) && below(y, z) ==> below(x, z)
  requires forall x, y :: below(a(x), y) == below(x, b(y))
  requires below(u, v)
  ensures below(a(u), a(v))
{
}

lemma FMonotonic'(u: T, v: T)
  requires Below(u, v)
  ensures Below(f(u), f(v))
{
  forall x | true {
    Reflexive(x);
  }
  forall x, y, z | true {
    Transitive(x, y, z);
  }
  forall x, y | true {
    Connection(x, y);
  }
  GeneralMonotonic(u, v, Below, f, g);
}

lemma GMonotonic(u: T, v: T)
  requires Below(u, v)
  ensures Below(g(u), g(v))
{
  forall x | true {
    AboveReflexive(x);
  }
  forall x, y, z | true {
    AboveTransitive(x, y, z);
  }
  forall x, y | true {
    calc {
      Above(g(x), y);
    ==
      Below(y, g(x));
    ==
      {
        Connection(y, x);
      }
      Below(f(y), x);
    ==
      Above(x, f(y));
    }
  }
  GeneralMonotonic(v, u, Above, g, f);
}

type T(!new)
