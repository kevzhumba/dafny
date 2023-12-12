
// NoTypeArgs.dfy

method M0()
{
  var l: List;
  l := Cons(5, Nil);
  assert l.hd == 5;
  var k: MyClass<bool>;
  k := new MyClass;
  k.data := false;
  var h := new MyClass;
  h.data := false;
  var y := new MyClass.Init(120);
  var z: int := y.data;
}

method M1()
{
  var l: List<int>;
  l := Cons(5, Nil);
  assert l.hd == 5;
  var k: MyClass<bool>;
  k := new MyClass<bool>;
  k.data := false;
  var h := new MyClass<bool>;
  h.data := true;
  var y := new MyClass<int>.Init(120);
  var z: int := y.data;
}

ghost function concat(xs: List, ys: List): List
{
  match xs
  case Nil =>
    ys
  case Cons(x, tail) =>
    Cons(x, concat(tail, ys))
}

ghost function reverse(xs: List): List
{
  match xs
  case Nil =>
    Nil
  case Cons(t, rest) =>
    concat(reverse(rest), Cons(t, Nil))
}

lemma Theorem(xs: List)
  ensures reverse(reverse(xs)) == xs
{
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(t, rest) =>
    Lemma(reverse(rest), Cons(t, Nil));
}

lemma Lemma<A>(xs: List, ys: List)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs))
{
  match xs
  case {:split false} Nil =>
    assert forall ws: List<A> {:induction} :: concat(ws, Nil) == ws;
  case {:split false} Cons(t, rest) =>
    assert forall a: List<A>, b, c {:induction} :: concat(a, concat(b, c)) == concat(concat(a, b), c);
}

method DoAPrefix<A, B, C>(xs: List) returns (ys: List<A>)
{
  ys := xs;
}

ghost function FDoAPrefix<A, B, C>(xs: List): List<A>
{
  xs
}

datatype List<T> = Nil | Cons(hd: T, tl: List)

class MyClass<G(0)> {
  var data: G

  method Init(g: G)
    modifies this
  {
    data := g;
  }
}
