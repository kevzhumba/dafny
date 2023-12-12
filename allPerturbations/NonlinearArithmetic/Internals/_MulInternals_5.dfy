include "GeneralInternals.dfy"
include "MulInternalsNonlinear.dfy"
// MulInternals.dfy


module {:options "-functionSyntax:4"} MulInternals {
  function {:opaque} MulPos(x: int, y: int): int
    requires x >= 0
  {
    if x == 0 then
      0
    else
      y + MulPos(x - 1, y)
  }

  function MulRecursive(x: int, y: int): int
  {
    if x >= 0 then
      MulPos(x, y)
    else
      -1 * MulPos(-1 * x, y)
  }

  lemma LemmaMulInduction(f: int -> bool)
    requires f(0)
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures forall i {:trigger f(i)} :: f(i)
  {
    forall i | true
      ensures f(i)
    {
      LemmaInductionHelper(1, f, i);
    }
  }

  lemma LemmaMulCommutes()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
    forall x: int, y: int | true
      ensures x * y == y * x
    {
      LemmaMulInduction(i => x * i == i * x);
    }
  }

  lemma LemmaMulSuccessor()
    ensures forall x: int, y: int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x: int, y: int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
    LemmaMulCommutes();
  }

  lemma LemmaMulDistributes()
    ensures forall x: int, y: int, z: int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x: int, y: int, z: int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
    LemmaMulSuccessor();
    forall x: int, y: int, z: int | true
      ensures (x + y) * z == x * z + y * z
      ensures (x - y) * z == x * z - y * z
    {
      var f1 := i => (x + i) * z == x * z + i * z;
      var f2 := i => (x - i) * z == x * z - i * z;
      assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == (x + i + 1) * z == (x + i) * z + z;
      assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == (x + i - 1) * z == (x + i) * z - z;
      assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == (x - i - 1) * z == (x - i) * z - z;
      assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == (x - i + 1) * z == (x - i) * z + z;
      LemmaMulInduction(f1);
      LemmaMulInduction(f2);
      assert f1(y);
      assert f2(y);
    }
  }

  ghost predicate MulAuto()
  {
    (forall x: int, y: int {:trigger x * y} :: 
      x * y == y * x) &&
    (forall x: int, y: int, z: int {:trigger (x + y) * z} :: 
      (x + y) * z == x * z + y * z) &&
    forall x: int, y: int, z: int {:trigger (x - y) * z} :: 
      (x - y) * z == x * z - y * z
  }

  lemma LemmaMulAuto()
    ensures MulAuto()
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
  }

  lemma LemmaMulInductionAuto(x: int, f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures f(x)
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
    assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInduction(f);
    assert f(x);
  }

  lemma LemmaMulInductionAutoForall(f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures forall i {:trigger f(i)} :: f(i)
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
    assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInduction(f);
  }

  import opened GeneralInternals

  import opened MulInternalsNonlinear
}
