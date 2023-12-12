
// NatList.dfy

method Main()
{
  var ns := Nil;
  ns := Cons(4, Cons(10, Nil));
  print "ns = ", ns, "\n";
  print "Sum(ns) = ", Sum(ns), "\n";
  var ns' := Cons(20, Nil);
  var ns'' := Append(ns, ns');
  print "ns' = ", ns', "\n";
  print "Append(ns, ns') = ", ns'', "\n";
  print "Sum(Append(ns, ns')) = ", Sum(ns''), "\n";
  ConvertAndPrint(ns, -12);
}

function Sum(ns: List<nat>): nat
{
  match ns
  case Nil =>
    0
  case Cons(n, tail) =>
    n + Sum(tail)
}

function Append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil =>
    ys
  case Cons(t, tail) =>
    Cons(t, Append(tail, ys))
}

function Negate(xs: List<int>): List<int>
{
  match xs
  case Nil =>
    Nil
  case Cons(x, tail) =>
    Cons(-x, Negate(tail))
}

lemma DoubleNegation(xs: List<int>)
  ensures Negate(Negate(xs)) == xs
{
}

method ConvertAndPrint(ns: List<nat>, nn: int)
  requires nn <= 0
{
  var xs := Negate(Negate(ns));
  DoubleNegation(ns);
  var ns': List<nat> := xs;
  print "Sum(Negate(Negate(ns))) = ", Sum(ns'), "\n";
  var negs := Cons(-3, Cons(0, Cons(-2, Nil)));
  var s := Sum(Negate(negs));
  print "negs = ", negs, "\n";
  print "Sum(Negate(negs)) = ", s, "\n";
  negs := Cons(-3, Cons(nn, Cons(-2, Nil)));
  NatTan(negs);
  var _ /* _v0 */ := Conversion_Int2Nat(Negate(negs));
  s := Sum(Negate(negs));
  print "negs = ", negs, "\n";
  print "Sum(Negate(negs)) = ", s, "\n";
}

lemma {:induction false} Conversion_Nat2Int(ns: List<nat>) returns (xs: List<int>)
  ensures ns == xs
{
  xs := ns;
}

ghost predicate ElementsAreNat(xs: List<int>)
{
  match xs
  case Nil =>
    true
  case Cons(x, tail) =>
    0 <= x &&
    ElementsAreNat(tail)
}

ghost predicate ElementsAreTan(xs: List<int>)
{
  match xs
  case Nil =>
    true
  case Cons(x, tail) =>
    x <= 0 &&
    ElementsAreTan(tail)
}

lemma NatTan(xs: List<int>)
  requires ElementsAreTan(xs)
  ensures ElementsAreNat(Negate(xs))
{
}

lemma {:induction false} Conversion_Int2Nat(xs: List<int>) returns (ns: List<nat>)
  requires ElementsAreNat(xs)
  ensures xs == ns
{
  match xs
  case {:split false} Nil =>
    ns := xs;
  case {:split false} Cons(x, tail) =>
    ns := Conversion_Int2Nat(tail);
    ns := Cons(x, ns);
}

datatype List<+T> = Nil | Cons(head: T, tail: List<T>)
