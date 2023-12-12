include "../../Wrappers.dfy"
// Maps.dfy


module {:options "-functionSyntax:4"} Maps {
  function Get<X, Y>(m: map<X, Y>, x: X): Option<Y>
  {
    if x in m then
      Some(m[x])
    else
      None
  }

  function {:opaque} ToImap<X, Y>(m: map<X, Y>): (m': imap<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m
  {
    imap x | x in m :: m[x]
  }

  function {:opaque} RemoveKeys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    m - xs
  }

  function {:opaque} Remove<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }

  function {:opaque} Restrict<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, m.Keys - xs)
  {
    map x | x in xs && x in m :: m[x]
  }

  ghost predicate EqualOnKey<X, Y>(m: map<X, Y>, m': map<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  ghost predicate IsSubset<X, Y>(m: map<X, Y>, m': map<X, Y>)
  {
    m.Keys <= m'.Keys &&
    forall x {:trigger EqualOnKey(m, m', x)} {:trigger x in m} :: 
      x in m ==>
        EqualOnKey(m, m', x)
  }

  function {:opaque} Union<X, Y>(m: map<X, Y>, m': map<X, Y>): (r: map<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x {:trigger r[x]} :: x in m' ==> r[x] == m'[x]
    ensures forall x {:trigger r[x]} :: x in m && x !in m' ==> r[x] == m[x]
  {
    m + m'
  }

  lemma LemmaDisjointUnionSize<X, Y>(m: map<X, Y>, m': map<X, Y>)
    requires m.Keys !! m'.Keys
    ensures |Union(m, m')| == |m| + |m'|
  {
    var u := Union(m, m');
    assert |u.Keys| == |m.Keys| + |m'.Keys|;
  }

  ghost predicate {:opaque} Injective<X, Y>(m: map<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: 
      x != x' &&
      x in m &&
      x' in m ==>
        m[x] != m[x']
  }

  ghost function {:opaque} Invert<X, Y>(m: map<X, Y>): map<Y, X>
  {
    map y | y in m.Values :: var x :| x in m.Keys && m[x] == y; x
  }

  lemma LemmaInvertIsInjective<X, Y>(m: map<X, Y>)
    ensures Injective(Invert(m))
  {
  }

  ghost predicate {:opaque} Total<X(!new), Y>(m: map<X, Y>)
  {
    forall i {:trigger m[i]} {:trigger i in m} :: 
      i in m
  }

  ghost predicate {:opaque} Monotonic(m: map<int, int>)
  {
    forall x, x' {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      x <= x' ==>
        m[x] <= m[x']
  }

  ghost predicate {:opaque} MonotonicFrom(m: map<int, int>, start: int)
  {
    forall x, x' {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      start <= x <= x' ==>
        m[x] <= m[x']
  }

  import opened Wrappers
}
