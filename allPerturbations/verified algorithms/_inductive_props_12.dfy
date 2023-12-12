
// inductive_props.dfy

ghost predicate even(n: nat)
{
  match n {
    case 0 =>
      true
    case 1 =>
      false
    case _ /* _v0 */ =>
      even(n - 2)
  }
}

lemma a0()
  ensures even(4)
{
}

lemma a1()
  ensures !even(3)
{
}

lemma a2(n: nat)
  requires even(n)
  ensures even(n + 2)
{
}

lemma a3(n: nat)
  requires even(n + 2)
  ensures even(n)
{
}

ghost predicate Even(n: nat)
{
  exists r: EvenRule :: 
    r.apply() == n
}

lemma b0()
  ensures Even(4)
{
  assert ev_SS(ev_SS(ev_0)).apply() == 4;
}

lemma b1()
  ensures !Even(3)
{
  if r: EvenRule :| r.apply() == 3 {
    assert r.ev_SS? && r.r.apply() == 1;
  }
}

lemma b2(n: nat)
  requires Even(n)
  ensures Even(n + 2)
{
  var r: EvenRule :| r.apply() == n;
  assert ev_SS(r).apply() == n + 2;
}

lemma b3(n: nat)
  requires Even(n + 2)
  ensures Even(n)
{
  var r: EvenRule :| r.apply() == n + 2;
  assert r.ev_SS? && r.r.apply() == n;
}

ghost predicate Ev(ev: P)
{
  ev(0) &&
  forall n: nat | ev(n) :: 
    ev(n + 2)
}

ghost predicate Minimal(Ev: P -> bool, ev: P)
{
  Ev(ev) &&
  forall ev': P, n: nat | Ev(ev') :: 
    ev(n) ==>
      ev'(n)
}

lemma c0(ev: P)
  requires Minimal(Ev, ev)
  ensures ev(4)
{
  assert ev(2);
}

lemma c1(ev: P)
  requires Minimal(Ev, ev)
  ensures !ev(3)
{
  var cex := (n: nat) => n != 1 && n != 3;
  assert Ev(cex);
}

lemma c2(ev: P, n: nat)
  requires Minimal(Ev, ev) && ev(n)
  ensures ev(n + 2)
{
}

lemma c3(ev: P, n: nat)
  requires Minimal(Ev, ev) && ev(n + 2)
  ensures ev(n)
{
}

lemma a_implies_b(n: nat)
  requires even(n)
  ensures Even(n)
{
  if n == 0 {
    assert ev_0.apply() == 0;
  } else {
    a_implies_b(n - 2);
    var r: EvenRule :| r.apply() == n - 2;
    assert ev_SS(r).apply() == n;
  }
}

lemma b_implies_c(ev: P, n: nat)
  requires Minimal(Ev, ev) && Even(n)
  ensures ev(n)
{
  var r: EvenRule :| r.apply() == n;
  if r.ev_SS? {
    assert r.r.apply() == n - 2;
    b_implies_c(ev, n - 2);
  }
}

lemma c_implies_a(ev: P, n: nat)
  requires Minimal(Ev, ev) && ev(n)
  ensures even(n)
{
  if n == 1 {
    var cex := (m: nat) => m != 1;
    assert Ev(cex);
  } else if n >= 2 {
    c3(ev, n - 2);
    c_implies_a(ev, n - 2);
  }
}

datatype EvenRule = ev_0 | ev_SS(r: EvenRule) {
  ghost function apply(): nat
  {
    match this {
      case ev_0 =>
        0
      case ev_SS(r) =>
        r.apply() + 2
    }
  }
}

type P = nat -> bool
