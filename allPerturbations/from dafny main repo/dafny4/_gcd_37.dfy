
// gcd.dfy

ghost predicate IsFactor(p: pos, x: pos)
{
  exists q :: 
    p * q == x
}

ghost function Factors(x: pos): set<pos>
{
  set p: pos | p <= x && IsFactor(p, x)
}

lemma FactorsHasAllFactors(x: pos)
  ensures forall n :: n in Factors(x) <==> n in iset p: pos | IsFactor(p, x)
{
}

lemma FactorsContains1(x: pos)
  ensures 1 in Factors(x)
{
  assert 1 * x == x;
}

lemma FactorsContainsSelf(x: pos)
  ensures x in Factors(x)
{
  assert x * 1 == x;
}

ghost function Max(s: set<pos>): pos
  requires s != {}
{
  MaxExists(s);
  var x :| x in s && forall y :: y in s ==> y <= x;
  x
}

lemma MaxExists(s: set<pos>)
  requires s != {}
  ensures exists x :: x in s && forall y :: y in s ==> y <= x
{
  var x := FindMax(s);
}

ghost function FindMax(s: set<pos>): (max: pos)
  requires s != {}
  ensures max in s && forall y :: y in s ==> y <= max
{
  var x :| x in s;
  if s == {x} then
    x
  else
    var s' := s - {x}; assert s == s' + {x}; var y := FindMax(s'); if x < y then y else x
}

ghost function Gcd(x: pos, y: pos): pos
{
  var common := Factors(x) * Factors(y);
  assert 1 in common by {
    FactorsContains1(x);
    FactorsContains1(y);
  }
  Max(common)
}

lemma AboutGcd(x: pos, y: pos)
  ensures IsFactor(Gcd(x, y), x)
  ensures IsFactor(Gcd(x, y), y)
  ensures forall p: pos :: IsFactor(p, x) && IsFactor(p, y) ==> p <= Gcd(x, y)
{
  forall p: pos | IsFactor(p, x) && IsFactor(p, y)
    ensures p <= Gcd(x, y)
  {
    assert p in Factors(x) * Factors(y);
  }
}

lemma GcdSymmetric(x: pos, y: pos)
  ensures Gcd(x, y) == Gcd(y, x)
{
  assert Factors(x) * Factors(y) == Factors(y) * Factors(x);
}

lemma GcdIdempotent(x: pos)
  ensures Gcd(x, x) == x
{
  FactorsContainsSelf(x);
  assert x in Factors(x) * Factors(x);
}

lemma GcdSubtract(x: pos, y: pos)
  requires x < y
  ensures Gcd(x, y) == Gcd(x, y - x)
{
  var p := Gcd(x, y);
  assert IsFactor(p, y - x) by {
    var a :| p * a == x;
    var b :| p * b == y;
    calc {
      y - x;
    ==
      p * b - p * a;
    ==
      p * (b - a);
    }
  }
  var common := Factors(x) * Factors(y - x);
  assert p in common;
  forall q | q in common
    ensures q <= p
  {
    var a :| q * a == x;
    var b :| q * b == y - x;
    assert IsFactor(q, y) by {
      calc {
        y;
      ==
        x + (y - x);
      ==
        q * a + q * b;
      ==
        q * (a + b);
      }
    }
    assert q in Factors(x) * Factors(y);
  }
}

method EuclidGcd(X: pos, Y: pos) returns (gcd: pos)
  ensures gcd == Gcd(X, Y)
{
  var x: pos, y: pos := X, Y;
  while
    invariant Gcd(x, y) == Gcd(X, Y)
    decreases x + y
  {
    case x < y =>
      GcdSubtract(x, y);
      y := y - x;
    case y < x =>
      calc {
        Gcd(x, y);
      ==
        {
          GcdSymmetric(x, y);
        }
        Gcd(y, x);
      ==
        {
          GcdSubtract(y, x);
        }
        Gcd(y, x - y);
      ==
        {
          GcdSymmetric(y, x - y);
        }
        Gcd(x - y, y);
      }
      x := x - y;
  }
  GcdIdempotent(x);
  return x;
}

lemma GcdSubtractAlt(x: pos, y: pos)
  requires x < y
  ensures Gcd(y, x) == Gcd(x, y - x)
{
  GcdSymmetric(x, y);
  var p := Gcd(x, y);
  assert IsFactor(p, y - x) by {
    var a :| p * a == x;
    var b :| p * b == y;
    calc {
      y - x;
    ==
      p * b - p * a;
    ==
      p * (b - a);
    }
  }
  var common := Factors(x) * Factors(y - x);
  assert p in common;
  forall q | q in common
    ensures q <= p
  {
    var a :| q * a == x;
    var b :| q * b == y - x;
    assert IsFactor(q, y) by {
      calc {
        y;
      ==
        x + (y - x);
      ==
        q * a + q * b;
      ==
        q * (a + b);
      }
    }
    assert q in Factors(x) * Factors(y);
  }
}

method EuclidGcdAlt(X: pos, Y: pos) returns (gcd: pos)
  ensures gcd == Gcd(X, Y)
{
  var x: pos, y: pos := X, Y;
  while
    invariant Gcd(x, y) == Gcd(X, Y)
    decreases x + y
  {
    case x < y =>
      GcdSubtractAlt(x, y);
      GcdSymmetric(y, x);
      y := y - x;
    case y < x =>
      GcdSymmetric(x - y, y);
      GcdSubtractAlt(y, x);
      x := x - y;
  }
  GcdIdempotent(x);
  return x;
}

method Main()
{
  Test(15, 9);
  Test(14, 22);
  Test(1, 2);
  Test(1, 1);
  Test(13, 13);
  Test(60, 60);
}

method Test(x: pos, y: pos)
{
  var gcd := EuclidGcd(x, y);
  print x, " gcd ", y, "  =  ", gcd, "\n";
}

type pos = x
  | 1 <= x
  witness 1
