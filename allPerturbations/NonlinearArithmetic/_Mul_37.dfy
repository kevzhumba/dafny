include "Internals/MulInternalsNonlinear.dfy"
include "Internals/MulInternals.dfy"
// Mul.dfy


module {:options "-functionSyntax:4"} Mul {
  lemma LemmaMulIsMulRecursive(x: int, y: int)
    ensures x * y == MulRecursive(x, y)
  {
    if x >= 0 {
      LemmaMulIsMulPos(x, y);
    }
    if x <= 0 {
      LemmaMulIsMulPos(-x, y);
    }
    LemmaMulAuto();
  }

  lemma LemmaMulIsMulRecursiveAuto()
    ensures forall x: int, y: int :: x * y == MulRecursive(x, y)
  {
    forall x: int, y: int | true
      ensures x * y == MulRecursive(x, y)
    {
      LemmaMulIsMulRecursive(x, y);
    }
  }

  lemma LemmaMulIsMulPos(x: int, y: int)
    requires x >= 0
    ensures x * y == MulPos(x, y)
  {
    reveal MulPos();
    LemmaMulInductionAuto(x, u => u >= 0 ==> u * y == MulPos(u, y));
  }

  lemma LemmaMulBasics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
  {
  }

  lemma LemmaMulBasicsAuto()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {
    MulINL.LemmaMulNonzero(x, y);
  }

  lemma LemmaMulNonzeroAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
    forall x: int, y: int | true
      ensures x * y != 0 <==> x != 0 && y != 0
    {
      LemmaMulNonzero(x, y);
    }
  }

  lemma LemmaMulByZeroIsZeroAuto()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x == 0
  {
    forall x: int {:trigger 0 * x} {:trigger x * 0} | true
      ensures x * 0 == 0 * x == 0
    {
      LemmaMulBasics(x);
    }
  }

  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * (y * z) == x * y * z
  {
    MulINL.LemmaMulIsAssociative(x, y, z);
  }

  lemma LemmaMulIsAssociativeAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)} {:trigger x * y * z} :: x * (y * z) == x * y * z
  {
    forall x: int, y: int, z: int | true
      ensures x * (y * z) == x * y * z
    {
      LemmaMulIsAssociative(x, y, z);
    }
  }

  lemma LemmaMulIsCommutative(x: int, y: int)
    ensures x * y == y * x
  {
  }

  lemma LemmaMulIsCommutativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {
    MulINL.LemmaMulOrdering(x, y);
  }

  lemma LemmaMulOrderingAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 != x && 0 != y && x * y >= 0 ==> x * y >= x && x * y >= y
  {
    forall x: int, y: int | 0 != x && 0 != y && x * y >= 0
      ensures x * y >= x && x * y >= y
    {
      LemmaMulOrdering(x, y);
    }
  }

  lemma LemmaMulEquality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
  {
  }

  lemma LemmaMulEqualityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x == y ==> x * z == y * z
  {
    forall x: int, y: int, z: int | x == y
      ensures x * z == y * z
    {
      LemmaMulEquality(x, y, z);
    }
  }

  lemma LemmaMulInequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures x * z <= y * z
  {
    LemmaMulInductionAuto(z, u => u >= 0 ==> x * u <= y * u);
  }

  lemma LemmaMulInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
    forall x: int, y: int, z: int | x <= y && z >= 0
      ensures x * z <= y * z
    {
      LemmaMulInequality(x, y, z);
    }
  }

  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
  {
    MulINL.LemmaMulStrictInequality(x, y, z);
  }

  lemma LemmaMulStrictInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
    forall x: int, y: int, z: int | x < y && z > 0
      ensures x * z < y * z
    {
      LemmaMulStrictInequality(x, y, z);
    }
  }

  lemma LemmaMulUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x <= XBound
    requires y <= YBound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= XBound * YBound
  {
    LemmaMulInequality(x, XBound, y);
    LemmaMulInequality(y, YBound, XBound);
  }

  lemma LemmaMulUpperBoundAuto()
    ensures forall x: int, XBound: int, y: int, YBound: int {:trigger x * y, XBound * YBound} :: x <= XBound && y <= YBound && 0 <= x && 0 <= y ==> x * y <= XBound * YBound
  {
    forall x: int, XBound: int, y: int, YBound: int | x <= XBound && y <= YBound && 0 <= x && 0 <= y
      ensures x * y <= XBound * YBound
    {
      LemmaMulUpperBound(x, XBound, y, YBound);
    }
  }

  lemma LemmaMulStrictUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x < XBound
    requires y < YBound
    requires 0 < x
    requires 0 < y
    ensures x * y <= (XBound - 1) * (YBound - 1)
  {
    LemmaMulInequality(x, XBound - 1, y);
    LemmaMulInequality(y, YBound - 1, XBound - 1);
  }

  lemma LemmaMulStrictUpperBoundAuto()
    ensures forall x: int, XBound: int, y: int, YBound: int {:trigger x * y, (XBound - 1) * (YBound - 1)} :: x < XBound && y < YBound && 0 < x && 0 < y ==> x * y <= (XBound - 1) * (YBound - 1)
  {
    forall x: int, XBound: int, y: int, YBound: int | x < XBound && y < YBound && 0 < x && 0 < y
      ensures x * y <= (XBound - 1) * (YBound - 1)
    {
      LemmaMulStrictUpperBound(x, XBound, y, YBound);
    }
  }

  lemma LemmaMulLeftInequality(x: int, y: int, z: int)
    requires 0 < x
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
  {
    LemmaMulInductionAuto(x, u => u > 0 ==> y <= z ==> u * y <= u * z);
    LemmaMulInductionAuto(x, u => u > 0 ==> y < z ==> u * y < u * z);
  }

  lemma LemmaMulLeftInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y, x * z} :: x > 0 ==> (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
  {
    forall x: int, y: int, z: int | (y <= z || y < z) && 0 < x
      ensures (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
    {
      LemmaMulLeftInequality(x, y, z);
    }
  }

  lemma LemmaMulEqualityConverse(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
  {
    LemmaMulInductionAuto(m, u => x > y && 0 < u ==> x * u > y * u);
    LemmaMulInductionAuto(m, u => x < y && 0 < u ==> x * u < y * u);
    LemmaMulInductionAuto(m, u => x < y && 0 > u ==> x * u > y * u);
  }

  lemma LemmaMulEqualityConverseAuto()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: m != 0 && m * x == m * y ==> x == y
  {
    forall m: int, x: int, y: int | m != 0 && m * x == m * y
      ensures x == y
    {
      LemmaMulEqualityConverse(m, x, y);
    }
  }

  lemma LemmaMulInequalityConverse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures x <= y
  {
    LemmaMulInductionAuto(z, u => x * u <= y * u && u > 0 ==> x <= y);
  }

  lemma LemmaMulInequalityConverseAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
    forall x: int, y: int, z: int | x * z <= y * z && z > 0
      ensures x <= y
    {
      LemmaMulInequalityConverse(x, y, z);
    }
  }

  lemma LemmaMulStrictInequalityConverse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures x < y
  {
    LemmaMulInductionAuto(z, u => x * u < y * u && u >= 0 ==> x < y);
  }

  lemma LemmaMulStrictInequalityConverseAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
    forall x: int, y: int, z: int | x * z < y * z && z >= 0
      ensures x < y
    {
      LemmaMulStrictInequalityConverse(x, y, z);
    }
  }

  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {
    MulINL.LemmaMulIsDistributiveAdd(x, y, z);
  }

  lemma LemmaMulIsDistributiveAddAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
    forall x: int, y: int, z: int | true
      ensures x * (y + z) == x * y + x * z
    {
      LemmaMulIsDistributiveAdd(x, y, z);
    }
  }

  lemma LemmaMulIsDistributiveAddOtherWay(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
  {
    LemmaMulAuto();
  }

  lemma LemmaMulIsDistributiveAddOtherWayAuto()
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
  {
    forall x: int, y: int, z: int | true
      ensures (y + z) * x == y * x + z * x
    {
      LemmaMulIsDistributiveAddOtherWay(x, y, z);
    }
  }

  lemma LemmaMulIsDistributiveSub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
  {
    LemmaMulAuto();
  }

  lemma LemmaMulIsDistributiveSubAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
    forall x: int, y: int, z: int | true
      ensures x * (y - z) == x * y - x * z
    {
      LemmaMulIsDistributiveSub(x, y, z);
    }
  }

  lemma LemmaMulIsDistributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
  {
    LemmaMulAuto();
  }

  lemma LemmaMulIsDistributiveAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
    LemmaMulIsDistributiveAddAuto();
    LemmaMulIsDistributiveSubAuto();
    LemmaMulIsCommutativeAuto();
  }

  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
  {
    MulINL.LemmaMulStrictlyPositive(x, y);
  }

  lemma LemmaMulStrictlyPositiveAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
    forall x: int, y: int | 0 < x && 0 < y
      ensures 0 < x * y
    {
      LemmaMulStrictlyPositive(x, y);
    }
  }

  lemma LemmaMulStrictlyIncreases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
  {
    LemmaMulInductionAuto(x, u => 1 < u ==> y < u * y);
  }

  lemma LemmaMulStrictlyIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
  {
    forall x: int, y: int | 1 < x && 0 < y
      ensures y < x * y
    {
      LemmaMulStrictlyIncreases(x, y);
    }
  }

  lemma LemmaMulIncreases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
  {
    LemmaMulInductionAuto(x, u => 0 < u ==> y <= u * y);
  }

  lemma LemmaMulIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
  {
    forall x: int, y: int | 0 < x && 0 < y
      ensures y <= x * y
    {
      LemmaMulIncreases(x, y);
    }
  }

  lemma LemmaMulNonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures 0 <= x * y
  {
    LemmaMulInductionAuto(x, u => 0 <= u ==> 0 <= u * y);
  }

  lemma LemmaMulNonnegativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
    forall x: int, y: int | 0 <= x && 0 <= y
      ensures 0 <= x * y
    {
      LemmaMulNonnegative(x, y);
    }
  }

  lemma LemmaMulUnaryNegation(x: int, y: int)
    ensures -x * y == -(x * y) == x * -y
  {
    LemmaMulInductionAuto(x, u => -u * y == -(u * y) == u * -y);
  }

  lemma LemmaMulUnaryNegationAuto()
    ensures forall x: int, y: int {:trigger -x * y} {:trigger x * -y} :: -x * y == -(x * y) == x * -y
  {
    forall x: int, y: int | true
      ensures -x * y == -(x * y) == x * -y
    {
      LemmaMulUnaryNegation(x, y);
    }
  }

  lemma LemmaMulCancelsNegatives(x: int, y: int)
    ensures x * y == -x * -y
  {
    LemmaMulUnaryNegationAuto();
  }

  lemma LemmaMulCancelsNegativesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == -x * -y
  {
    forall x: int, y: int | true
      ensures x * y == -x * -y
    {
      LemmaMulCancelsNegatives(x, y);
    }
  }

  lemma LemmaMulProperties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1} {:trigger 1 * x} :: x * 1 == 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)} {:trigger x * y * z} :: x * (y * z) == x * y * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
    LemmaMulStrictInequalityAuto();
    LemmaMulInequalityAuto();
    LemmaMulIsDistributiveAuto();
    LemmaMulIsAssociativeAuto();
    LemmaMulOrderingAuto();
    LemmaMulNonzeroAuto();
    LemmaMulNonnegativeAuto();
    LemmaMulStrictlyIncreasesAuto();
    LemmaMulIncreasesAuto();
  }

  import MulINL = MulInternalsNonlinear

  import opened MulInternals
}
