include "../../Wrappers.dfy"
// Imaps.dfy


module {:options "-functionSyntax:4"} Imaps {
  function Get<X, Y>(m: imap<X, Y>, x: X): Option<Y>
  {
    if x in m then
      Some(m[x])
    else
      None
  }

  ghost function {:opaque} RemoveKeys<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    imap x | x in m && x !in xs :: m[x]
  }

  ghost function {:opaque} RemoveKey<X, Y>(m: imap<X, Y>, x: X): (m': imap<X, Y>)
    ensures m' == RemoveKeys(m, iset{x})
    ensures forall x' {:trigger m'[x']} :: x' in m' ==> m'[x'] == m[x']
  {
    imap i | i in m && i != x :: m[i]
  }

  ghost function {:opaque} Restrict<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures m' == RemoveKeys(m, m.Keys - xs)
  {
    imap x | x in xs && x in m :: m[x]
  }

  ghost predicate EqualOnKey<X, Y>(m: imap<X, Y>, m': imap<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  ghost predicate IsSubset<X, Y>(m: imap<X, Y>, m': imap<X, Y>)
  {
    m.Keys <= m'.Keys &&
    forall x {:trigger EqualOnKey(m, m', x)} {:trigger x in m} :: 
      x in m ==>
        EqualOnKey(m, m', x)
  }

  ghost function {:opaque} Union<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (r: imap<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x {:trigger r[x]} :: x in m' ==> r[x] == m'[x]
    ensures forall x {:trigger r[x]} :: x in m && x !in m' ==> r[x] == m[x]
  {
    m + m'
  }

  ghost predicate {:opaque} Injective<X, Y>(m: imap<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: 
      x != x' &&
      x in m &&
      x' in m ==>
        m[x] != m[x']
  }

  ghost function {:opaque} Invert<X, Y>(m: imap<X, Y>): imap<Y, X>
  {
    imap y | y in m.Values :: var x :| x in m.Keys && m[x] == y; x
  }

  lemma LemmaInvertIsInjective<X, Y>(m: imap<X, Y>)
    ensures Injective(Invert(m))
  {
    reveal Invert();
  }

  ghost predicate {:opaque} Total<X(!new), Y>(m: imap<X, Y>)
  {
    forall i {:trigger m[i]} {:trigger i in m} :: 
      i in m
  }

  ghost predicate {:opaque} Monotonic(m: imap<int, int>)
  {
    forall x, x' {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      x <= x' ==>
        m[x] <= m[x']
  }

  ghost predicate {:opaque} MonotonicFrom(m: imap<int, int>, start: int)
  {
    forall x, x' {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      start <= x <= x' ==>
        m[x] <= m[x']
  }

  import opened Wrappers
}
