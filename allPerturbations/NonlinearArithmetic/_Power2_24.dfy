include "Internals/GeneralInternals.dfy"
include "Internals/MulInternals.dfy"
include "Power.dfy"
// Power2.dfy


module {:options "-functionSyntax:4"} Power2 {
  function {:opaque} Pow2(e: nat): nat
    ensures Pow2(e) > 0
  {
    reveal Pow();
    LemmaPowPositive(2, e);
    Pow(2, e)
  }

  lemma LemmaPow2(e: nat)
    ensures Pow2(e) == Pow(2, e)
  {
    reveal Pow();
    reveal Pow2();
    if e != 0 {
      LemmaPow2(e - 1);
    }
  }

  lemma LemmaPow2Auto()
    ensures forall e: nat {:trigger Pow2(e)} :: Pow2(e) == Pow(2, e)
  {
    reveal Pow();
    reveal Pow2();
    forall e: nat {:trigger Pow2(e)} | true
      ensures Pow2(e) == Pow(2, e)
    {
      LemmaPow2(e);
    }
  }

  lemma LemmaPow2MaskDiv2(e: nat)
    requires 0 < e
    ensures (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
  {
    LemmaPow2Auto();
    LemmaPowAuto();
    var f := e => 0 < e ==> (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1;
    assert forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInductionAuto(e, f);
  }

  lemma LemmaPow2MaskDiv2Auto()
    ensures forall e: nat {:trigger Pow2(e)} :: 0 < e ==> (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
  {
    reveal Pow2();
    forall e: nat {:trigger Pow2(e)} | 0 < e
      ensures (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
    {
      LemmaPow2MaskDiv2(e);
    }
  }

  lemma Lemma2To64()
    ensures Pow2(0) == 1
    ensures Pow2(1) == 2
    ensures Pow2(2) == 4
    ensures Pow2(3) == 8
    ensures Pow2(4) == 16
    ensures Pow2(5) == 32
    ensures Pow2(6) == 64
    ensures Pow2(7) == 128
    ensures Pow2(8) == 256
    ensures Pow2(9) == 512
    ensures Pow2(10) == 1024
    ensures Pow2(11) == 2048
    ensures Pow2(12) == 4096
    ensures Pow2(13) == 8192
    ensures Pow2(14) == 16384
    ensures Pow2(15) == 32768
    ensures Pow2(16) == 65536
    ensures Pow2(17) == 131072
    ensures Pow2(18) == 262144
    ensures Pow2(19) == 524288
    ensures Pow2(20) == 1048576
    ensures Pow2(21) == 2097152
    ensures Pow2(22) == 4194304
    ensures Pow2(23) == 8388608
    ensures Pow2(24) == 16777216
    ensures Pow2(25) == 33554432
    ensures Pow2(26) == 67108864
    ensures Pow2(27) == 134217728
    ensures Pow2(28) == 268435456
    ensures Pow2(29) == 536870912
    ensures Pow2(30) == 1073741824
    ensures Pow2(31) == 2147483648
    ensures Pow2(32) == 4294967296
    ensures Pow2(64) == 18446744073709551616
  {
    reveal Pow2();
  }

  import opened GeneralInternals

  import opened MulInternals

  import opened Power
}
