
// Bug124.dfy

ghost function power(n: nat, e: nat): int

lemma lemma_power()
  ensures forall n: nat, e: nat :: 0 <= n * e && power(n, e) == 5
{
}
