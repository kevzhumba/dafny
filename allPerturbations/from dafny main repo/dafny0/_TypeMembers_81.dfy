
// TypeMembers.dfy

method Main()
{
  BasicTests();
  MoreTests();
}

method BasicTests()
{
  var t := Yes;
  var r := t.W();
  var q := t.Q() + DaTy.Q();
  print t, " ", r, " ", q, "\n";
  var p: Pos := 8;
  print p, " ";
  var u := Pos.Func(p);
  assert u == 11;
  print u, " ";
  var v := p.Gittit();
  assert v == 10;
  print v, " ";
  var w := Pos.Method(p);
  assert w == 11;
  print w, " ";
  var x := p.Collect();
  assert x == 10;
  print x, " ";
  print "\n";
}

method MoreTests()
{
  var d := Business(true, 5);
  var v := d.G(5);
  var u := Dt<int>.G(7);
  print d.F(10), " ", v, " ", u, "\n";
  print Dt<real>.g, " ", d.g, "\n";
  var yy, dd := d.M(93);
  print yy, " ", dd, "\n";
  var a0 := d.P(54);
  var a1 := Dt<bool>.P(55);
  print a0, " ", a1, "\n";
  print d.c, "\n";
  var c: Co<real> := Cobalt;
  print Co<bv11>.g, " ", c.g, "\n";
  print c.F(2), " ", Co<bv11>.G(70), " ", c.G(71), "\n";
  var c';
  yy, c' := c.M(93);
  print yy, " ", c, "\n";
  a0 := c.P(54);
  a1 := Co<bool>.P(55);
  print a0, " ", a1, "\n";
  print c.c, "\n";
  var pr: Primes := 11;
  print pr, " ", Primes.g, " ", pr.g, " ", pr.c, "\n";
  print pr.F(2), " ", Primes.G(70), " ", pr.G(71), "\n";
  yy, pr := pr.M(95);
  print yy, " ", pr, "\n";
  a0 := pr.P(54);
  a1 := Primes.P(55);
  print a0, " ", a1, "\n";
  var sm: Small := 11;
  print sm, " ", Small.g, " ", sm.g, " ", sm.c, "\n";
  print sm.F(2), " ", Small.G(70), " ", sm.G(71), "\n";
  yy, sm := sm.M(95);
  print yy, " ", sm, "\n";
  a0 := sm.P(54);
  a1 := Small.P(55);
  print a0, " ", a1, "\n";
}

datatype DaTy = Yes {
  function W(): int
  {
    10
  }

  static function Q(): int
  {
    13
  }
}

newtype Pos = x
  | 0 < x
  witness 1
{
  static function Func(y: Pos): int
  {
    (y + 3) as int
  }

  function Gittit(): int
  {
    (this + 2) as int
  }

  static method Method(y: Pos) returns (r: int)
    ensures r == (y + 3) as int
  {
    return (y + 3) as int;
  }

  method Collect() returns (r: int)
    ensures r == (this + 2) as int
  {
    return (this + 2) as int;
  }
}

datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, a: A) {
  const c: int := if this.Blue? then 18 else 19
  static const g: int := 22

  function F(x: int): int
  {
    x + if this.Bucket? then this.diameter.Floor else 25
  }

  static function G(x: int): int
  {
    2 * x
  }

  method M(x: int) returns (y: int, d: Dt<A>)
  {
    if this == Blue {
      y := x;
    } else {
      y := 9;
    }
    var z := RecursiveZero(3);
    y := y + z;
    z := StaticRecursiveZero(3);
    y := y + z;
    match this
    case {:split false} Blue =>
      assert y == x;
      d := Bucket(0.0);
    case {:split false} Bucket(dm) =>
      d := this.(diameter := this.diameter + 2.0);
    case {:split false} Business(t, a) =>
      d := this.(trendy := !t);
  }

  static method P(x: int) returns (y: int)
  {
    y := x + g;
  }

  twostate predicate Toop()
  {
    old(this) == this
  }

  twostate lemma Tool()
  {
  }

  least predicate IndP()
  {
    true
  }

  greatest predicate CoP()
  {
    true
  }

  method RecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x != 0 {
      return 0;
    } else {
      z := RecursiveZero(0);
    }
  }

  static method StaticRecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := StaticRecursiveZero(0);
    }
  }
}

codatatype Co<A> = Cobalt | Continues(next: Co<A>) {
  const c: int := if this.Cobalt? then 18 else 19
  static const g: int

  function F(x: int): int
  {
    19
  }

  static function G(x: int): int
  {
    x + 12
  }

  method M(x: int) returns (y: int, d: Co<int>)
  {
    if this == Cobalt {
      y := x;
    } else {
      y := 9;
    }
    var z := RecursiveZero(3);
    y := y + z;
    z := StaticRecursiveZero(3);
    y := y + z;
    d := Cobalt;
  }

  static method P(x: int) returns (y: int)
  {
    y := x / 2;
  }

  method RecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := RecursiveZero(0);
    }
  }

  static method StaticRecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := StaticRecursiveZero(0);
    }
  }
}

newtype Primes = x
  | 2 <= x && forall y :: 2 <= y < x ==> x % y != 0
  witness 2
{
  const c: int := this as int * 2
  static const g: int := 18

  function F(x: int): int
  {
    2 * x + this as int
  }

  static function G(x: int): int
  {
    100 - x
  }

  method M(x: int) returns (y: int, d: Primes)
  {
    var z := RecursiveZero(3);
    return x + z, this;
  }

  static method P(x: int) returns (y: int)
  {
    var z := StaticRecursiveZero(3);
    y := 3 * x + z;
  }

  method RecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := RecursiveZero(0);
    }
  }

  static method StaticRecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := StaticRecursiveZero(0);
    }
  }
}

newtype Small = x
  | 0 <= x < 25
{
  const c := this as int % 4
  static const g: int := 18

  function F(x: int): int
  {
    2 * x + this as int
  }

  static function G(x: int): int
  {
    100 - x
  }

  method M(x: int) returns (y: int, d: Small)
  {
    var z := RecursiveZero(3);
    return x + z, this;
  }

  static method P(x: int) returns (y: int)
  {
    var z := StaticRecursiveZero(3);
    y := 3 * x + z;
  }

  method RecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := RecursiveZero(0);
    }
  }

  static method StaticRecursiveZero(x: int) returns (z: int)
    ensures z == 0
    decreases x != 0
  {
    if x == 0 {
      return 0;
    } else {
      z := StaticRecursiveZero(0);
    }
  }
}
