include "Internals/DivInternalsNonlinear.dfy"
include "Internals/DivInternals.dfy"
include "Internals/GeneralInternals.dfy"
// DivMod.dfy


module {:options "-functionSyntax:4"} DivMod {
  lemma LemmaDivIsDivRecursive(x: int, d: int)
    requires 0 < d
    ensures DivRecursive(x, d) == x / d
  {
    reveal DivPos();
    reveal DivRecursive();
    LemmaDivInductionAuto(d, x, u => DivRecursive(u, d) == u / d);
  }

  lemma LemmaDivIsDivRecursiveAuto()
    ensures forall x: int, d: int {:trigger x / d} :: d > 0 ==> DivRecursive(x, d) == x / d
  {
    reveal DivPos();
    reveal DivRecursive();
    forall x: int, d: int | d > 0
      ensures DivRecursive(x, d) == x / d
    {
      LemmaDivIsDivRecursive(x, d);
    }
  }

  lemma LemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
  {
    DivINL.LemmaDivBySelf(d);
  }

  lemma LemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
  {
    DivINL.LemmaDivOf0(d);
  }

  lemma LemmaDivBasics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
  {
    if x != 0 {
      LemmaDivBySelf(x);
      LemmaDivOf0(x);
    }
  }

  lemma LemmaDivBasicsAuto()
    ensures forall x {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x {:trigger x / 1} :: x / 1 == x
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
    forall x: int | true
      ensures x != 0 ==> 0 / x == 0
      ensures x / 1 == x
    {
      LemmaDivBasics(x);
    }
    forall x: int, y: int | x >= 0 && y > 0
      ensures 0 <= x / y <= x
    {
      LemmaDivPosIsPos(x, y);
      LemmaDivIsOrderedByDenominator(x, 1, y);
    }
  }

  lemma LemmaSmallDivConverseAuto()
    ensures forall x, d {:trigger x / d} :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
    forall x, d | 0 <= x && 0 < d && x / d == 0
      ensures x < d
    {
      LemmaDivInductionAuto(d, x, u => 0 <= u && 0 < d && u / d == 0 ==> u < d);
    }
  }

  lemma LemmaDivNonZero(x: int, d: int)
    requires x >= d > 0
    ensures x / d > 0
  {
    LemmaDivPosIsPosAuto();
    if x / d == 0 {
      LemmaSmallDivConverseAuto();
    }
  }

  lemma LemmaDivNonZeroAuto()
    ensures forall x, d {:trigger x / d} | x >= d > 0 :: x / d > 0
  {
    forall x, d | x >= d > 0 {
      LemmaDivNonZero(x, d);
    }
  }

  lemma LemmaDivIsOrderedByDenominator(x: int, y: int, z: int)
    requires 0 <= x
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
    reveal DivPos();
    reveal DivRecursive();
    LemmaDivIsDivRecursiveAuto();
    assert forall u: int, d: int {:trigger u / d} {:trigger DivRecursive(u, d)} :: d > 0 ==> DivRecursive(u, d) == u / d;
    if x < z {
      LemmaDivIsOrdered(0, x, y);
    } else {
      LemmaDivIsOrdered(x - z, x - y, y);
      LemmaDivIsOrderedByDenominator(x - z, y, z);
    }
  }

  lemma LemmaDivIsOrderedByDenominatorAuto()
    ensures forall x: int, y: int, z: int {:trigger x / y, x / z} :: 0 <= x && 1 <= y <= z ==> x / y >= x / z
  {
    forall x: int, y: int, z: int | 0 <= x && 1 <= y <= z
      ensures x / y >= x / z
    {
      LemmaDivIsOrderedByDenominator(x, y, z);
    }
  }

  lemma LemmaDivIsStrictlyOrderedByDenominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x
  {
    LemmaDivInductionAuto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma LemmaDivIsStrictlyOrderedByDenominatorAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall x: int, d: int | 0 < x && 1 < d
      ensures x / d < x
    {
      LemmaDivIsStrictlyOrderedByDenominator(x, d);
    }
  }

  lemma LemmaDividingSums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * ((a + b) / d) - R == d * (a / d) + d * (b / d)
  {
    calc ==> {
      a % d + b % d == R + (a + b) % d;
      a + b - (a + b) % d - R == a - a % d + b - b % d;
      {
        LemmaFundamentalDivMod(a + b, d);
        LemmaFundamentalDivMod(a, d);
        LemmaFundamentalDivMod(b, d);
      }
      d * ((a + b) / d) - R == d * (a / d) + d * (b / d);
    }
  }

  lemma LemmaDividingSumsAuto()
    ensures forall a: int, b: int, d: int, R: int {:trigger d * ((a + b) / d) - R, d * (a / d) + d * (b / d)} :: 0 < d && R == a % d + b % d - (a + b) % d ==> d * ((a + b) / d) - R == d * (a / d) + d * (b / d)
  {
    forall a: int, b: int, d: int, R: int | 0 < d && R == a % d + b % d - (a + b) % d
      ensures d * ((a + b) / d) - R == d * (a / d) + d * (b / d)
    {
      LemmaDividingSums(a, b, d, R);
    }
  }

  lemma LemmaDivPosIsPos(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x / d
  {
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u / d >= 0);
  }

  lemma LemmaDivPosIsPosAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> 0 <= x / d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures 0 <= x / d
    {
      LemmaDivPosIsPos(x, d);
    }
  }

  lemma LemmaDivPlusOne(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
  {
    LemmaDivAuto(d);
  }

  lemma LemmaDivPlusOneAuto()
    ensures forall x: int, d: int {:trigger 1 + x / d, (d + x) / d} :: 0 < d ==> 1 + x / d == (d + x) / d
  {
    forall x: int, d: int | 0 < d
      ensures 1 + x / d == (d + x) / d
    {
      LemmaDivPlusOne(x, d);
    }
  }

  lemma LemmaDivMinusOne(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
  {
    LemmaDivAuto(d);
  }

  lemma LemmaDivMinusOneAuto()
    ensures forall x: int, d: int {:trigger -1 + x / d, (-d + x) / d} :: 0 < d ==> -1 + x / d == (-d + x) / d
  {
    forall x: int, d: int | 0 < d
      ensures -1 + x / d == (-d + x) / d
    {
      LemmaDivMinusOne(x, d);
    }
  }

  lemma LemmaBasicDiv(d: int)
    requires 0 < d
    ensures forall x {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    LemmaDivAuto(d);
  }

  lemma LemmaBasicDivAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    forall x: int, d: int | 0 <= x < d
      ensures x / d == 0
    {
      LemmaBasicDiv(d);
    }
  }

  lemma LemmaDivIsOrdered(x: int, y: int, z: int)
    requires x <= y
    requires 0 < z
    ensures x / z <= y / z
  {
    LemmaDivInductionAuto(z, x - y, xy => xy <= 0 ==> (xy + y) / z <= y / z);
  }

  lemma LemmaDivIsOrderedAuto()
    ensures forall x: int, y: int, z: int {:trigger x / z, y / z} :: x <= y && 0 < z ==> x / z <= y / z
  {
    forall x: int, y: int, z: int | x <= y && 0 < z
      ensures x / z <= y / z
    {
      LemmaDivIsOrdered(x, y, z);
    }
  }

  lemma LemmaDivDecreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
  {
    LemmaDivInductionAuto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma LemmaDivDecreasesAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall x: int, d: int | 0 < x && 1 < d
      ensures x / d < x
    {
      LemmaDivDecreases(x, d);
    }
  }

  lemma LemmaDivNonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d <= x
  {
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u / d <= u);
  }

  lemma LemmaDivNonincreasingAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> x / d <= x
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x / d <= x
    {
      LemmaDivNonincreasing(x, d);
    }
  }

  lemma LemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
  {
    ModINL.LemmaSmallMod(x, m);
  }

  lemma LemmaBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures 0 < y * z
    ensures x % (y * z) == y * (x / y % z) + x % y
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaDivPosIsPos(x, y);
    assert 0 <= x / y;
    calc {
      y * (x / y) % (y * z) + x % y % (y * z);
    <=
      {
        LemmaPartBound1(x, y, z);
      }
      y * (z - 1) + x % y % (y * z);
    <
      {
        LemmaPartBound2(x, y, z);
      }
      y * (z - 1) + y;
      {
        LemmaMulBasicsAuto();
      }
      y * (z - 1) + y * 1;
      {
        LemmaMulIsDistributiveAuto();
      }
      y * (z - 1 + 1);
      y * z;
    }
    calc {
      x % (y * z);
      {
        LemmaFundamentalDivMod(x, y);
      }
      (y * (x / y) + x % y) % (y * z);
      {
        LemmaModPropertiesAuto();
        assert 0 <= x % y;
        LemmaMulNonnegative(y, x / y);
        assert y * (x / y) % (y * z) + x % y % (y * z) < y * z;
        LemmaModAdds(y * (x / y), x % y, y * z);
      }
      y * (x / y) % (y * z) + x % y % (y * z);
      {
        LemmaModPropertiesAuto();
        LemmaMulIncreases(z, y);
        LemmaMulIsCommutativeAuto();
        assert x % y < y <= y * z;
        LemmaSmallMod(x % y, y * z);
        assert x % y % (y * z) == x % y;
      }
      y * (x / y) % (y * z) + x % y;
      {
        LemmaTruncateMiddle(x / y, y, z);
      }
      y * (x / y % z) + x % y;
    }
  }

  lemma LemmaBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % (y * z), y * (x / y % z) + x % y} :: 0 <= x && 0 < y && 0 < z ==> 0 < y * z && x % (y * z) == y * (x / y % z) + x % y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z
      ensures 0 < y * z && x % (y * z) == y * (x / y % z) + x % y
    {
      LemmaBreakdown(x, y, z);
    }
  }

  lemma LemmaRemainderUpper(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x - d < x / d * d
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u - d < u / d * d);
  }

  lemma LemmaRemainderUpperAuto()
    ensures forall x: int, d: int {:trigger x - d, d * d} :: 0 <= x && 0 < d ==> x - d < x / d * d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x - d < x / d * d
    {
      LemmaRemainderUpper(x, d);
    }
  }

  lemma LemmaRemainderLower(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x >= x / d * d
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u >= u / d * d);
  }

  lemma LemmaRemainderLowerAuto()
    ensures forall x: int, d: int {:trigger x / d * d} :: 0 <= x && 0 < d ==> x >= x / d * d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x >= x / d * d
    {
      LemmaRemainderLower(x, d);
    }
  }

  lemma LemmaRemainder(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x - x / d * d < d
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, x, u => 0 <= u - u / d * d < d);
  }

  lemma LemmaRemainderAuto()
    ensures forall x: int, d: int {:trigger x - x / d * d} :: 0 <= x && 0 < d ==> 0 <= x - x / d * d < d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures 0 <= x - x / d * d < d
    {
      LemmaRemainder(x, d);
    }
  }

  lemma LemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + x % d
  {
    ModINL.LemmaFundamentalDivMod(x, d);
  }

  lemma LemmaFundamentalDivModAuto()
    ensures forall x: int, d: int {:trigger d * (x / d) + x % d} :: d != 0 ==> x == d * (x / d) + x % d
  {
    forall x: int, d: int | d != 0
      ensures x == d * (x / d) + x % d
    {
      LemmaFundamentalDivMod(x, d);
    }
  }

  lemma LemmaDivDenominator(x: int, c: nat, d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures x / c / d == x / (c * d)
  {
    LemmaMulStrictlyPositiveAuto();
    var R := x % (c * d);
    LemmaModPropertiesAuto();
    LemmaDivPosIsPos(R, c);
    if R / c >= d {
      LemmaFundamentalDivMod(R, c);
      LemmaMulInequality(d, R / c, c);
      LemmaMulIsCommutativeAuto();
      assert false;
    }
    assert R / c < d;
    LemmaMulBasicsAuto();
    LemmaFundamentalDivModConverse(R / c, d, 0, R / c);
    assert R / c % d == R / c;
    LemmaFundamentalDivMod(R, c);
    assert c * (R / c) + R % c == R;
    assert c * (R / c % d) + R % c == R;
    var k := x / (c * d);
    LemmaFundamentalDivMod(x, c * d);
    assert x == c * d * (x / (c * d)) + x % (c * d);
    assert R == x - c * d * (x / (c * d));
    assert R == x - c * d * k;
    calc {
      c * (x / c % d) + x % c;
      {
        LemmaModMultiplesVanish(-k, x / c, d);
        LemmaMulIsCommutativeAuto();
      }
      c * ((x / c + -k * d) % d) + x % c;
      {
        LemmaHoistOverDenominator(x, -k * d, c);
      }
      c * ((x + -k * d * c) / c % d) + x % c;
      {
        LemmaMulIsAssociative(-k, d, c);
      }
      c * ((x + -k * (d * c)) / c % d) + x % c;
      {
        LemmaMulUnaryNegation(k, d * c);
      }
      c * ((x + -(k * (d * c))) / c % d) + x % c;
      {
        LemmaMulIsAssociative(k, d, c);
      }
      c * ((x + -(k * d * c)) / c % d) + x % c;
      c * ((x - k * d * c) / c % d) + x % c;
      {
        LemmaMulIsAssociativeAuto();
        LemmaMulIsCommutativeAuto();
      }
      c * (R / c % d) + x % c;
      c * (R / c) + x % c;
      {
        LemmaFundamentalDivMod(R, c);
        assert R == c * (R / c) + R % c;
        LemmaModMod(x, c, d);
        assert R % c == x % c;
      }
      R;
      {
        LemmaModIsModRecursiveAuto();
      }
      R % (c * d);
      (x - c * d * k) % (c * d);
      {
        LemmaMulUnaryNegation(c * d, k);
      }
      (x + c * d * -k) % (c * d);
      {
        LemmaModMultiplesVanish(-k, x, c * d);
      }
      x % (c * d);
    }
    calc ==> {
      c * (x / c) + x % c - R == c * (x / c) - c * (x / c % d);
      {
        LemmaFundamentalDivMod(x, c);
      }
      x - R == c * (x / c) - c * (x / c % d);
    }
    calc ==> {
      true;
      {
        LemmaFundamentalDivMod(x / c, d);
      }
      d * (x / c / d) == x / c - x / c % d;
      c * (d * (x / c / d)) == c * (x / c - x / c % d);
      {
        LemmaMulIsAssociativeAuto();
      }
      c * d * (x / c / d) == c * (x / c - x / c % d);
      {
        LemmaMulIsDistributiveAuto();
      }
      c * d * (x / c / d) == c * (x / c) - c * (x / c % d);
      c * d * (x / c / d) == x - R;
      {
        LemmaFundamentalDivMod(x, c * d);
      }
      c * d * (x / c / d) == c * d * (x / (c * d)) + x % (c * d) - R;
      c * d * (x / c / d) == c * d * (x / (c * d));
      {
        LemmaMulEqualityConverse(c * d, x / c / d, x / (c * d));
      }
      x / c / d == x / (c * d);
    }
  }

  lemma LemmaDivDenominatorAuto()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger x / c / d} :: 0 <= x && 0 < c && 0 < d ==> x / c / d == x / (c * d)
  {
    LemmaMulNonzeroAuto();
    forall x: int, c: nat, d: nat | 0 <= x && 0 < c && 0 < d
      ensures x / c / d == x / (c * d)
    {
      LemmaDivDenominator(x, c, d);
    }
  }

  lemma LemmaMulHoistInequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * (y / z) <= x * y / z
  {
    calc {
      x * y / z;
      {
        LemmaFundamentalDivMod(y, z);
      }
      x * (z * (y / z) + y % z) / z;
      {
        LemmaMulIsDistributiveAuto();
      }
      (x * (z * (y / z)) + x * (y % z)) / z;
    >=
      {
        LemmaModPropertiesAuto();
        LemmaMulNonnegative(x, y % z);
        LemmaDivIsOrdered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z);
      }
      x * (z * (y / z)) / z;
      {
        LemmaMulIsAssociativeAuto();
        LemmaMulIsCommutativeAuto();
      }
      z * (x * (y / z)) / z;
      {
        LemmaDivMultiplesVanish(x * (y / z), z);
      }
      x * (y / z);
    }
  }

  lemma LemmaMulHoistInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y / z), x * y / z} :: 0 <= x && 0 < z ==> x * (y / z) <= x * y / z
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < z
      ensures x * (y / z) <= x * y / z
    {
      LemmaMulHoistInequality(x, y, z);
    }
  }

  lemma LemmaIndistinguishableQuotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
  {
    LemmaDivInductionAuto(d, a - b, ab => var u := ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d);
  }

  lemma LemmaIndistinguishableQuotientsAuto()
    ensures forall a: int, b: int, d: int {:trigger a / d, b / d} :: 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> a / d == b / d
  {
    forall a: int, b: int, d: int | 0 < d && 0 <= a - a % d <= b < a + d - a % d
      ensures a / d == b / d
    {
      LemmaIndistinguishableQuotients(a, b, d);
    }
  }

  lemma LemmaTruncateMiddle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * x % (b * c) == b * (x % c)
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaMulNonnegativeAuto();
    calc {
      b * x;
      {
        LemmaFundamentalDivMod(b * x, b * c);
      }
      b * c * (b * x / (b * c)) + b * x % (b * c);
      {
        LemmaDivDenominator(b * x, b, c);
      }
      b * c * (b * x / b / c) + b * x % (b * c);
      {
        LemmaMulIsCommutativeAuto();
        LemmaDivByMultiple(x, b);
      }
      b * c * (x / c) + b * x % (b * c);
    }
    calc ==> {
      true;
      {
        LemmaFundamentalDivMod(x, c);
      }
      x == c * (x / c) + x % c;
      b * x == b * (c * (x / c) + x % c);
      {
        LemmaMulIsDistributiveAuto();
      }
      b * x == b * (c * (x / c)) + b * (x % c);
      {
        LemmaMulIsAssociativeAuto();
      }
      b * x == b * c * (x / c) + b * (x % c);
    }
  }

  lemma LemmaTruncateMiddleAuto()
    ensures forall x: int, b: int, c: int {:trigger b * (x % c)} :: 0 <= x && 0 < b && 0 < c && 0 < b * c ==> b * x % (b * c) == b * (x % c)
  {
    forall x: int, b: int, c: int | 0 <= x && 0 < b && 0 < c && 0 < b * c
      ensures b * x % (b * c) == b * (x % c)
    {
      LemmaTruncateMiddle(x, b, c);
    }
  }

  lemma LemmaDivMultiplesVanishQuotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == x * a / (x * d)
  {
    LemmaMulStrictlyPositive(x, d);
    calc {
      x * a / (x * d);
      {
        LemmaMulNonnegative(x, a);
        LemmaDivDenominator(x * a, x, d);
      }
      x * a / x / d;
      {
        LemmaDivMultiplesVanish(a, x);
      }
      a / d;
    }
  }

  lemma LemmaDivMultiplesVanishQuotientAuto()
    ensures forall x: int, a: int, d: int {:trigger a / d, x * d, x * a} :: 0 < x && 0 <= a && 0 < d ==> 0 < x * d && a / d == x * a / (x * d)
  {
    forall x: int, a: int, d: int | 0 < x && 0 <= a && 0 < d
      ensures 0 < x * d && a / d == x * a / (x * d)
    {
      LemmaDivMultiplesVanishQuotient(x, a, d);
    }
  }

  lemma LemmaRoundDown(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * ((a + r) / d)
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, a, u => u % d == 0 ==> u == d * ((u + r) / d));
  }

  lemma LemmaRoundDownAuto()
    ensures forall a: int, r: int, d: int {:trigger d * ((a + r) / d)} :: 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d)
  {
    forall a: int, r: int, d: int | 0 < d && a % d == 0 && 0 <= r < d
      ensures a == d * ((a + r) / d)
    {
      LemmaRoundDown(a, r, d);
    }
  }

  lemma LemmaDivMultiplesVanishFancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
  {
    LemmaDivAuto(d);
    var f := u => (d * u + b) / d == u;
    LemmaMulInductionAuto(x, f);
    assert f(x);
  }

  lemma LemmaDivMultiplesVanishFancyAuto()
    ensures forall x: int, b: int, d: int {:trigger (d * x + b) / d} :: 0 < d && 0 <= b < d ==> (d * x + b) / d == x
  {
    forall x: int, b: int, d: int | 0 < d && 0 <= b < d
      ensures (d * x + b) / d == x
    {
      LemmaDivMultiplesVanishFancy(x, b, d);
    }
  }

  lemma LemmaDivMultiplesVanish(x: int, d: int)
    requires 0 < d
    ensures d * x / d == x
  {
    LemmaDivMultiplesVanishFancy(x, 0, d);
  }

  lemma LemmaDivMultiplesVanishAuto()
    ensures forall x: int, d: int {:trigger d * x / d} :: 0 < d ==> d * x / d == x
  {
    forall x: int, d: int | 0 < d
      ensures d * x / d == x
    {
      LemmaDivMultiplesVanish(x, d);
    }
  }

  lemma LemmaDivByMultiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures b * d / d == b
  {
    LemmaDivMultiplesVanish(b, d);
  }

  lemma LemmaDivByMultipleAuto()
    ensures forall b: int, d: int {:trigger b * d / d} :: 0 <= b && 0 < d ==> b * d / d == b
  {
    forall b: int, d: int | 0 <= b && 0 < d
      ensures b * d / d == b
    {
      LemmaDivByMultiple(b, d);
    }
  }

  lemma LemmaDivByMultipleIsStronglyOrdered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires 0 < z
    ensures x / z < y / z
  {
    LemmaModMultiplesBasic(m, z);
    LemmaDivInductionAuto(z, y - x, yx => var u := yx + x; x < u && u % z == 0 ==> x / z < u / z);
  }

  lemma LemmaDivByMultipleIsStronglyOrderedAuto()
    ensures forall x: int, y: int, m: int, z: int {:trigger x / z, m * z, y / z} :: x < y && y == m * z && 0 < z ==> x / z < y / z
  {
    forall x: int, y: int, m: int, z: int | x < y && y == m * z && 0 < z
      ensures x / z < y / z
    {
      LemmaDivByMultipleIsStronglyOrdered(x, y, m, z);
    }
  }

  lemma LemmaMultiplyDivideLe(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures a / b <= c
  {
    LemmaModMultiplesBasic(c, b);
    LemmaDivInductionAuto(b, b * c - a, i => 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b);
    LemmaDivMultiplesVanish(c, b);
  }

  lemma LemmaMultiplyDivideLeAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a <= b * c ==> a / b <= c
  {
    forall a: int, b: int, c: int | 0 < b && a <= b * c
      ensures a / b <= c
    {
      LemmaMultiplyDivideLe(a, b, c);
    }
  }

  lemma LemmaMultiplyDivideLt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures a / b < c
  {
    LemmaModMultiplesBasic(c, b);
    LemmaDivInductionAuto(b, b * c - a, i => 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b);
    LemmaDivMultiplesVanish(c, b);
  }

  lemma LemmaMultiplyDivideLtAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a < b * c ==> a / b < c
  {
    forall a: int, b: int, c: int | 0 < b && a < b * c
      ensures a / b < c
    {
      LemmaMultiplyDivideLt(a, b, c);
    }
  }

  lemma LemmaHoistOverDenominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
  {
    LemmaDivAuto(d);
    LemmaMulInductionAuto(j, u => x / d + u == (x + u * d) / d);
  }

  lemma LemmaHoistOverDenominatorAuto()
    ensures forall x: int, j: int, d: nat {:trigger x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
  {
    forall x: int, j: int, d: nat | 0 < d
      ensures x / d + j == (x + j * d) / d
    {
      LemmaHoistOverDenominator(x, j, d);
    }
  }

  lemma LemmaPartBound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * (a / b) % (b * c) <= b * (c - 1)
  {
    LemmaMulStrictlyPositiveAuto();
    calc {
      b * (a / b) % (b * c);
      {
        LemmaFundamentalDivMod(b * (a / b), b * c);
      }
      b * (a / b) - b * c * (b * (a / b) / (b * c));
      {
        LemmaMulIsAssociativeAuto();
      }
      b * (a / b) - b * (c * (b * (a / b) / (b * c)));
      {
        LemmaMulIsDistributiveAuto();
      }
      b * (a / b - c * (b * (a / b) / (b * c)));
    }
    calc ==> {
      true;
      {
        LemmaModPropertiesAuto();
      }
      b * (a / b) % (b * c) < b * c;
      b * (a / b - c * (b * (a / b) / (b * c))) < b * c;
      {
        LemmaMulIsCommutativeAuto();
        LemmaMulStrictInequalityConverseAuto();
      }
      a / b - c * (b * (a / b) / (b * c)) < c;
      a / b - c * (b * (a / b) / (b * c)) <= c - 1;
      {
        LemmaMulIsCommutativeAuto();
        LemmaMulInequalityAuto();
      }
      b * (a / b - c * (b * (a / b) / (b * c))) <= b * (c - 1);
      b * (a / b) % (b * c) <= b * (c - 1);
    }
  }

  lemma LemmaPartBound1Auto()
    ensures forall a: int, b: int, c: int {:trigger b * (a / b) % (b * c)} :: 0 <= a && 0 < b && 0 < c ==> 0 < b * c && b * (a / b) % (b * c) <= b * (c - 1)
  {
    forall a: int, b: int, c: int | 0 <= a && 0 < b && 0 < c
      ensures 0 < b * c && b * (a / b) % (b * c) <= b * (c - 1)
    {
      LemmaPartBound1(a, b, c);
    }
  }

  lemma LemmaModIsModRecursive(x: int, m: int)
    requires m > 0
    ensures ModRecursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
    reveal ModRecursive();
    if x < 0 {
      calc {
        ModRecursive(x, m);
        ModRecursive(x + m, m);
        {
          LemmaModIsModRecursive(x + m, m);
        }
        (x + m) % m;
        {
          LemmaAddModNoop(x, m, m);
        }
        (x % m + m % m) % m;
        {
          LemmaModBasicsAuto();
        }
        x % m % m;
        {
          LemmaModBasicsAuto();
        }
        x % m;
      }
    } else if x < m {
      LemmaSmallMod(x, m);
    } else {
      calc {
        ModRecursive(x, m);
        ModRecursive(x - m, m);
        {
          LemmaModIsModRecursive(x - m, m);
        }
        (x - m) % m;
        {
          LemmaSubModNoop(x, m, m);
        }
        (x % m - m % m) % m;
        {
          LemmaModBasicsAuto();
        }
        x % m % m;
        {
          LemmaModBasicsAuto();
        }
        x % m;
      }
    }
  }

  lemma LemmaModIsModRecursiveAuto()
    ensures forall x: int, d: int {:trigger x % d} :: d > 0 ==> ModRecursive(x, d) == x % d
  {
    reveal ModRecursive();
    forall x: int, d: int | d > 0
      ensures ModRecursive(x, d) == x % d
    {
      LemmaModIsModRecursive(x, d);
    }
  }

  lemma LemmaModBasicsAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
  {
    forall m: int | m > 0
      ensures m % m == 0
    {
      LemmaModAuto(m);
    }
    forall x: int, m: int | m > 0
      ensures x % m % m == x % m
    {
      LemmaModAuto(m);
    }
  }

  lemma LemmaModPropertiesAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: m > 0 ==> 0 <= x % m < m
  {
    forall x: int, m: int | m > 0
      ensures 0 <= x % m < m
    {
      LemmaModAuto(m);
    }
  }

  lemma LemmaModDecreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
  {
    LemmaModAuto(m);
  }

  lemma LemmaModDecreasesAuto()
    ensures forall x: nat, m: nat {:trigger x % m} :: 0 < m ==> x % m <= x
  {
    forall x: nat, m: nat | 0 < m
      ensures x % m <= x
    {
      LemmaModDecreases(x, m);
    }
  }

  lemma LemmaModIsZero(x: nat, m: nat)
    requires x > 0 && m > 0
    requires x % m == 0
    ensures x >= m
  {
    calc ==> {
      x < m;
      {
        LemmaSmallMod(x, m);
      }
      x % m == x;
      false;
    }
  }

  lemma LemmaModIsZeroAuto()
    ensures forall x: nat, m: nat {:trigger x % m} :: x > 0 && m > 0 && x % m == 0 ==> x >= m
  {
    forall x: nat, m: nat | x > 0 && m > 0 && x % m == 0
      ensures x >= m
    {
      LemmaModIsZero(x, m);
    }
  }

  lemma LemmaModMultiplesBasic(x: int, m: int)
    requires m > 0
    ensures x * m % m == 0
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(x, u => u * m % m == 0);
  }

  lemma LemmaModMultiplesBasicAuto()
    ensures forall x: int, m: int {:trigger x * m % m} :: m > 0 ==> x * m % m == 0
  {
    forall x: int, m: int | m > 0
      ensures x * m % m == 0
    {
      LemmaModMultiplesBasic(x, m);
    }
  }

  lemma LemmaModAddMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaModAddMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m
      ensures (m + b) % m == b % m
    {
      LemmaModAddMultiplesVanish(b, m);
    }
  }

  lemma LemmaModSubMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaModSubMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (-m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m
      ensures (-m + b) % m == b % m
    {
      LemmaModSubMultiplesVanish(b, m);
    }
  }

  lemma LemmaModMultiplesVanish(a: int, b: int, m: int)
    requires 0 < m
    ensures (m * a + b) % m == b % m
    decreases if a > 0 then a else -a
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(a, u => (m * u + b) % m == b % m);
  }

  lemma LemmaModMultiplesVanishAuto()
    ensures forall a: int, b: int, m: int {:trigger (m * a + b) % m} :: 0 < m ==> (m * a + b) % m == b % m
  {
    forall a: int, b: int, m: int | 0 < m
      ensures (m * a + b) % m == b % m
    {
      LemmaModMultiplesVanish(a, b, m);
    }
  }

  lemma LemmaModSubtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
  {
    LemmaModAuto(d);
  }

  lemma LemmaModSubtractionAuto()
    ensures forall x: nat, s: nat, d: nat {:trigger (x - s) % d} :: 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d
  {
    forall x: nat, s: nat, d: nat | 0 < d && 0 <= s <= x % d
      ensures x % d - s % d == (x - s) % d
    {
      LemmaModSubtraction(x, s, d);
    }
  }

  lemma LemmaAddModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m + y % m) % m == (x + y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaAddModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m} :: 0 < m ==> (x % m + y % m) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m + y % m) % m == (x + y) % m
    {
      LemmaAddModNoop(x, y, m);
    }
  }

  lemma LemmaAddModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + y % m) % m == (x + y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaAddModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m} :: 0 < m ==> (x + y % m) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x + y % m) % m == (x + y) % m
    {
      LemmaAddModNoopRight(x, y, m);
    }
  }

  lemma LemmaSubModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m - y % m) % m == (x - y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaSubModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} :: 0 < m ==> (x % m - y % m) % m == (x - y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m - y % m) % m == (x - y) % m
    {
      LemmaSubModNoop(x, y, m);
    }
  }

  lemma LemmaSubModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - y % m) % m == (x - y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaSubModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} :: 0 < m ==> (x - y % m) % m == (x - y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x - y % m) % m == (x - y) % m
    {
      LemmaSubModNoopRight(x, y, m);
    }
  }

  lemma LemmaModAdds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)
    ensures a % d + b % d < d ==> a % d + b % d == (a + b) % d
  {
    LemmaMulAuto();
    LemmaDivAuto(d);
  }

  lemma LemmaModAddsAuto()
    ensures forall a: int, b: int, d: int {:trigger (a + b) % d} :: 0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d) && (a % d + b % d < d ==> a % d + b % d == (a + b) % d)
  {
    forall a: int, b: int, d: int | 0 < d
      ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d) && (a % d + b % d < d ==> a % d + b % d == (a + b) % d)
    {
      LemmaModAdds(a, b, d);
    }
  }

  lemma {:vcs_split_on_every_assert} LemmaModNegNeg(x: int, d: int)
    requires 0 < d
    ensures x % d == x * (1 - d) % d
  {
    assert (x - x * d) % d == x % d by {
      LemmaModAuto(d);
      var f := i => (x - i * d) % d == x % d;
      assert MulAuto() ==> f(0) && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
      LemmaMulInductionAuto(x, f);
    }
    LemmaMulAuto();
  }

  lemma {:timeLimitMultiplier 5} LemmaFundamentalDivModConverse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d
    ensures r == x % d
  {
    LemmaDivAuto(d);
    LemmaMulInductionAuto(q, u => u == (u * d + r) / d);
    LemmaMulInductionAuto(q, u => r == (u * d + r) % d);
  }

  lemma {:timeLimitMultiplier 5} LemmaFundamentalDivModConverseAuto()
    ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d} :: d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d && r == x % d
  {
    forall x: int, d: int, q: int, r: int | d != 0 && 0 <= r < d && x == q * d + r
      ensures q == x / d && r == x % d
    {
      LemmaFundamentalDivModConverse(x, d, q, r);
    }
  }

  lemma LemmaModPosBound(x: int, m: int)
    requires 0 <= x
    requires 0 < m
    ensures 0 <= x % m < m
    decreases x
  {
    LemmaModAuto(m);
  }

  lemma LemmaModPosBoundAuto()
    ensures forall x: int, m: int {:trigger x % m} :: 0 <= x && 0 < m ==> 0 <= x % m < m
  {
    forall x: int, m: int | 0 <= x && 0 < m
      ensures 0 <= x % m < m
    {
      LemmaModPosBound(x, m);
    }
  }

  lemma LemmaMulModNoopLeft(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(y, u => x % m * u % m == x * u % m);
  }

  lemma LemmaMulModNoopLeftAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x % m * y % m == x * y % m
    {
      LemmaMulModNoopLeft(x, y, m);
    }
  }

  lemma LemmaMulModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == x * y % m
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(x, u => u * (y % m) % m == u * y % m);
  }

  lemma LemmaMulModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x * (y % m) % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x * (y % m) % m == x * y % m
    {
      LemmaMulModNoopRight(x, y, m);
    }
  }

  lemma LemmaMulModNoopGeneral(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    ensures x * (y % m) % m == x * y % m
    ensures x % m * (y % m) % m == x * y % m
  {
    LemmaModPropertiesAuto();
    LemmaMulModNoopLeft(x, y, m);
    LemmaMulModNoopRight(x, y, m);
    LemmaMulModNoopRight(x % m, y, m);
  }

  lemma LemmaMulModNoopGeneralAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m == x * (y % m) % m == x % m * (y % m) % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x % m * y % m == x * (y % m) % m == x % m * (y % m) % m == x * y % m
    {
      LemmaMulModNoopGeneral(x, y, m);
    }
  }

  lemma LemmaMulModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * (y % m) % m == x * y % m
  {
    LemmaMulModNoopGeneral(x, y, m);
  }

  lemma LemmaMulModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * (y % m) % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x % m * (y % m) % m == x * y % m
    {
      LemmaMulModNoop(x, y, m);
    }
  }

  lemma LemmaModEquivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    LemmaModAuto(m);
  }

  lemma LemmaModEquivalenceAuto()
    ensures forall x: int, y: int, m: int {:trigger x % m, y % m} :: 0 < m && x % m == y % m <==> 0 < m && (x - y) % m == 0
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x % m == y % m <==> 0 < m && (x - y) % m == 0
    {
      LemmaModEquivalence(x, y, m);
    }
  }

  ghost predicate IsModEquivalent(x: int, y: int, m: int)
    requires m > 0
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    LemmaModEquivalence(x, y, m);
    (x - y) % m == 0
  }

  lemma LemmaModMulEquivalent(x: int, y: int, z: int, m: int)
    requires m > 0
    requires IsModEquivalent(x, y, m)
    ensures IsModEquivalent(x * z, y * z, m)
  {
    LemmaMulModNoopLeft(x, z, m);
    LemmaMulModNoopLeft(y, z, m);
  }

  lemma LemmaModMulEquivalentAuto()
    ensures forall x: int, y: int, z: int, m: int {:trigger IsModEquivalent(x * z, y * z, m)} :: m > 0 && IsModEquivalent(x, y, m) ==> IsModEquivalent(x * z, y * z, m)
  {
    forall x: int, y: int, z: int, m: int | m > 0 && IsModEquivalent(x, y, m)
      ensures IsModEquivalent(x * z, y * z, m)
    {
      LemmaModMulEquivalent(x, y, z, m);
    }
  }

  lemma LemmaModOrdering(x: int, k: int, d: int)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
  {
    LemmaMulStrictlyIncreases(d, k);
    calc {
      x % d + d * (x / d);
      {
        LemmaFundamentalDivMod(x, d);
      }
      x;
      {
        LemmaFundamentalDivMod(x, d * k);
      }
      x % (d * k) + d * k * (x / (d * k));
      {
        LemmaMulIsAssociativeAuto();
      }
      x % (d * k) + d * (k * (x / (d * k)));
    }
    calc {
      x % d;
      {
        LemmaModPropertiesAuto();
      }
      x % d % d;
      {
        LemmaModMultiplesVanish(x / d - k * (x / (d * k)), x % d, d);
      }
      (x % d + d * (x / d - k * (x / (d * k)))) % d;
      {
        LemmaMulIsDistributiveSubAuto();
      }
      (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d;
      x % (d * k) % d;
    <=
      {
        LemmaModPropertiesAuto();
        LemmaModDecreases(x % (d * k), d);
      }
      x % (d * k);
    }
  }

  lemma LemmaModOrderingAuto()
    ensures forall x: int, k: int, d: int {:trigger x % (d * k)} :: 1 < d && 0 < k ==> 0 < d * k && x % d <= x % (d * k)
  {
    forall x: int, k: int, d: int | 1 < d && 0 < k
      ensures d * k > 0 && x % d <= x % (d * k)
    {
      LemmaModOrdering(x, k, d);
    }
  }

  lemma LemmaModMod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures x % (a * b) % a == x % a
  {
    LemmaMulStrictlyPositiveAuto();
    calc {
      x;
      {
        LemmaFundamentalDivMod(x, a * b);
      }
      a * b * (x / (a * b)) + x % (a * b);
      {
        LemmaMulIsAssociativeAuto();
      }
      a * (b * (x / (a * b))) + x % (a * b);
      {
        LemmaFundamentalDivMod(x % (a * b), a);
      }
      a * (b * (x / (a * b))) + a * (x % (a * b) / a) + x % (a * b) % a;
      {
        LemmaMulIsDistributiveAuto();
      }
      a * (b * (x / (a * b)) + x % (a * b) / a) + x % (a * b) % a;
    }
    LemmaModPropertiesAuto();
    LemmaMulIsCommutativeAuto();
    LemmaFundamentalDivModConverse(x, a, b * (x / (a * b)) + x % (a * b) / a, x % (a * b) % a);
  }

  lemma LemmaModModAuto()
    ensures forall x: int, a: int, b: int {:trigger a * b, x % a} :: 0 < a && 0 < b ==> 0 < a * b && x % (a * b) % a == x % a
  {
    forall x: int, a: int, b: int | 0 < a && 0 < b
      ensures 0 < a * b && x % (a * b) % a == x % a
    {
      LemmaModMod(x, a, b);
    }
  }

  lemma LemmaPartBound2(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % y % (y * z) < y
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaModPropertiesAuto();
    assert x % y < y;
    LemmaMulIncreasesAuto();
    LemmaMulIsCommutativeAuto();
    assert y <= y * z;
    assert 0 <= x % y < y * z;
    LemmaModPropertiesAuto();
    LemmaSmallMod(x % y, y * z);
    assert x % y % (y * z) == x % y;
  }

  lemma LemmaPartBound2Auto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % y} :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % y % (y * z) < y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z
      ensures y * z > 0 && x % y % (y * z) < y
    {
      LemmaPartBound2(x, y, z);
    }
  }

  lemma LemmaModBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % (y * z) == y * (x / y % z) + x % y
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaDivPosIsPos(x, y);
    assert 0 <= x / y;
    calc {
      y * (x / y) % (y * z) + x % y % (y * z);
    <=
      {
        LemmaPartBound1(x, y, z);
      }
      y * (z - 1) + x % y % (y * z);
    <
      {
        LemmaPartBound2(x, y, z);
      }
      y * (z - 1) + y;
      {
        LemmaMulBasicsAuto();
      }
      y * (z - 1) + y * 1;
      {
        LemmaMulIsDistributiveAuto();
      }
      y * (z - 1 + 1);
      y * z;
    }
    calc {
      x % (y * z);
      {
        LemmaFundamentalDivMod(x, y);
      }
      (y * (x / y) + x % y) % (y * z);
      {
        LemmaModPropertiesAuto();
        assert 0 <= x % y;
        LemmaMulNonnegative(y, x / y);
        assert y * (x / y) % (y * z) + x % y % (y * z) < y * z;
        LemmaModAdds(y * (x / y), x % y, y * z);
      }
      y * (x / y) % (y * z) + x % y % (y * z);
      {
        LemmaModPropertiesAuto();
        LemmaMulIncreases(z, y);
        LemmaMulIsCommutativeAuto();
        assert x % y < y <= y * z;
        LemmaSmallMod(x % y, y * z);
        assert x % y % (y * z) == x % y;
      }
      y * (x / y) % (y * z) + x % y;
      {
        LemmaTruncateMiddle(x / y, y, z);
      }
      y * (x / y % z) + x % y;
    }
  }

  lemma LemmaModBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger x % (y * z)} :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % (y * z) == y * (x / y % z) + x % y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z
      ensures y * z > 0 && x % (y * z) == y * (x / y % z) + x % y
    {
      LemmaModBreakdown(x, y, z);
    }
  }

  import opened DivInternals

  import DivINL = DivInternalsNonlinear

  import opened ModInternals

  import ModINL = ModInternalsNonlinear

  import opened MulInternals

  import opened Mul

  import opened GeneralInternals
}
