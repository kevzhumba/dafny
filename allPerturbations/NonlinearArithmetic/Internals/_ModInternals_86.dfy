include "GeneralInternals.dfy"
include "MulInternals.dfy"
include "../Mul.dfy"
include "ModInternalsNonlinear.dfy"
include "DivInternalsNonlinear.dfy"
// ModInternals.dfy


module {:options "-functionSyntax:4"} ModInternals {
  function {:opaque} ModRecursive(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      ModRecursive(d + x, d)
    else if x < d then
      x
    else
      ModRecursive(x - d, d)
  }

  lemma LemmaModInductionForall(n: int, f: int -> bool)
    requires n > 0
    requires forall i :: 0 <= i < n ==> f(i)
    requires forall i {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures forall i :: f(i)
  {
    forall i | true
      ensures f(i)
    {
      LemmaInductionHelper(n, f, i);
    }
  }

  lemma LemmaModInductionForall2(n: int, f: (int, int) -> bool)
    requires n > 0
    requires forall i, j :: 0 <= i < n && 0 <= j < n ==> f(i, j)
    requires forall i, j {:trigger f(i, j), f(i + n, j)} :: i >= 0 && f(i, j) ==> f(i + n, j)
    requires forall i, j {:trigger f(i, j), f(i, j + n)} :: j >= 0 && f(i, j) ==> f(i, j + n)
    requires forall i, j {:trigger f(i, j), f(i - n, j)} :: i < n && f(i, j) ==> f(i - n, j)
    requires forall i, j {:trigger f(i, j), f(i, j - n)} :: j < n && f(i, j) ==> f(i, j - n)
    ensures forall i, j :: f(i, j)
  {
    forall x, y | true
      ensures f(x, y)
    {
      forall i | 0 <= i < n
        ensures f(i, y)
      {
        var fj := j => f(i, j);
        LemmaModInductionForall(n, fj);
        assert fj(y);
      }
      var fi := i => f(i, y);
      LemmaModInductionForall(n, fi);
      assert fi(x);
    }
  }

  lemma LemmaDivAddDenominator(n: int, x: int)
    requires n > 0
    ensures (x + n) / n == x / n + 1
  {
    LemmaFundamentalDivMod(x, n);
    LemmaFundamentalDivMod(x + n, n);
    var zp := (x + n) / n - x / n - 1;
    forall
      ensures 0 == n * zp + (x + n) % n - x % n
    {
      LemmaMulAuto();
    }
    if zp > 0 {
      LemmaMulInequality(1, zp, n);
    }
    if zp < 0 {
      LemmaMulInequality(zp, -1, n);
    }
  }

  lemma LemmaDivSubDenominator(n: int, x: int)
    requires n > 0
    ensures (x - n) / n == x / n - 1
  {
    LemmaFundamentalDivMod(x, n);
    LemmaFundamentalDivMod(x - n, n);
    var zm := (x - n) / n - x / n + 1;
    forall
      ensures 0 == n * zm + (x - n) % n - x % n
    {
      LemmaMulAuto();
    }
    if zm > 0 {
      LemmaMulInequality(1, zm, n);
    }
    if zm < 0 {
      LemmaMulInequality(zm, -1, n);
    }
  }

  lemma LemmaModAddDenominator(n: int, x: int)
    requires n > 0
    ensures (x + n) % n == x % n
  {
    LemmaFundamentalDivMod(x, n);
    LemmaFundamentalDivMod(x + n, n);
    var zp := (x + n) / n - x / n - 1;
    forall
      ensures 0 == n * zp + (x + n) % n - x % n
    {
      LemmaMulAuto();
    }
    if zp > 0 {
      LemmaMulInequality(1, zp, n);
    }
    if zp < 0 {
      LemmaMulInequality(zp, -1, n);
    }
  }

  lemma LemmaModSubDenominator(n: int, x: int)
    requires n > 0
    ensures (x - n) % n == x % n
  {
    LemmaFundamentalDivMod(x - n, n);
    var zm := (x - n) / n - x / n + 1;
    forall
      ensures 0 == n * zm + (x - n) % n - x % n
    {
      LemmaMulAuto();
    }
    if zm > 0 {
      LemmaMulInequality(1, zm, n);
    }
    if zm < 0 {
      LemmaMulInequality(zm, -1, n);
    }
  }

  lemma LemmaModBelowDenominator(n: int, x: int)
    requires n > 0
    ensures 0 <= x < n <==> x % n == x
  {
    forall x: int | true
      ensures 0 <= x < n <==> x % n == x
    {
      if 0 <= x < n {
        LemmaSmallMod(x, n);
      }
      LemmaModRange(x, n);
    }
  }

  lemma LemmaModBasics(n: int)
    requires n > 0
    ensures forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
    ensures forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    ensures forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
  {
    forall x: int | true
      ensures (x + n) % n == x % n
      ensures (x - n) % n == x % n
      ensures (x + n) / n == x / n + 1
      ensures (x - n) / n == x / n - 1
      ensures 0 <= x < n <==> x % n == x
    {
      LemmaModBelowDenominator(n, x);
      LemmaModAddDenominator(n, x);
      LemmaModSubDenominator(n, x);
      LemmaDivAddDenominator(n, x);
      LemmaDivSubDenominator(n, x);
    }
  }

  lemma {:vcs_split_on_every_assert} LemmaQuotientAndRemainder(x: int, q: int, r: int, n: int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures q == x / n
    ensures r == x % n
    decreases if q > 0 then q else -q
  {
    LemmaModBasics(n);
    if q > 0 {
      MulInternalsNonlinear.LemmaMulIsDistributiveAdd(n, q - 1, 1);
      LemmaMulIsCommutativeAuto();
      assert q * n + r == (q - 1) * n + n + r;
      LemmaQuotientAndRemainder(x - n, q - 1, r, n);
    } else if q < 0 {
      Mul.LemmaMulIsDistributiveSub(n, q + 1, 1);
      LemmaMulIsCommutativeAuto();
      assert q * n + r == (q + 1) * n - n + r;
      LemmaQuotientAndRemainder(x + n, q + 1, r, n);
    } else {
      LemmaSmallDiv();
      assert r / n == 0;
    }
  }

  ghost predicate ModAuto(n: int)
    requires n > 0
  {
    n % n == -n % n == 0 &&
    (forall x: int {:trigger x % n % n} :: 
      x % n % n == x % n) &&
    (forall x: int {:trigger x % n} :: 
      0 <= x < n <==> x % n == x) &&
    (forall x: int, y: int {:trigger (x + y) % n} :: 
      var z := x % n + y % n; (0 <= z < n && (x + y) % n == z) || (n <= z < n + n && (x + y) % n == z - n)) &&
    forall x: int, y: int {:trigger (x - y) % n} :: 
      var z := x % n - y % n; (0 <= z < n && (x - y) % n == z) || (-n <= z < 0 && (x - y) % n == z + n)
  }

  lemma LemmaModAuto(n: int)
    requires n > 0
    ensures ModAuto(n)
  {
    LemmaModBasics(n);
    LemmaMulIsCommutativeAuto();
    LemmaMulIsDistributiveAddAuto();
    LemmaMulIsDistributiveSubAuto();
    forall x: int, y: int {:trigger (x + y) % n} | true
      ensures var z := x % n + y % n; (0 <= z < n && (x + y) % n == z) || (n <= z < 2 * n && (x + y) % n == z - n)
    {
      var xq, xr := x / n, x % n;
      LemmaFundamentalDivMod(x, n);
      assert x == xq * n + xr;
      var yq, yr := y / n, y % n;
      LemmaFundamentalDivMod(y, n);
      assert y == yq * n + yr;
      if xr + yr < n {
        LemmaQuotientAndRemainder(x + y, xq + yq, xr + yr, n);
      } else {
        LemmaQuotientAndRemainder(x + y, xq + yq + 1, xr + yr - n, n);
      }
    }
    forall x: int, y: int {:trigger (x - y) % n} | true
      ensures var z := x % n - y % n; (0 <= z < n && (x - y) % n == z) || (-n <= z < 0 && (x - y) % n == z + n)
    {
      var xq, xr := x / n, x % n;
      LemmaFundamentalDivMod(x, n);
      assert x == xq * n + xr;
      var yq, yr := y / n, y % n;
      LemmaFundamentalDivMod(y, n);
      assert y == yq * n + yr;
      if xr - yr >= 0 {
        LemmaQuotientAndRemainder(x - y, xq - yq, xr - yr, n);
      } else {
        LemmaQuotientAndRemainder(x - y, xq - yq - 1, xr - yr + n, n);
      }
    }
  }

  lemma LemmaModInductionAuto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures f(x)
  {
    LemmaModAuto(n);
    assert forall i :: IsLe(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
    LemmaModInductionForall(n, f);
    assert f(x);
  }

  lemma LemmaModInductionAutoForall(n: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures forall i {:trigger f(i)} :: f(i)
  {
    LemmaModAuto(n);
    assert forall i :: IsLe(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
    LemmaModInductionForall(n, f);
  }

  import opened GeneralInternals

  import opened Mul

  import opened MulInternalsNonlinear

  import opened MulInternals

  import opened ModInternalsNonlinear

  import opened DivInternalsNonlinear
}
