
// SharedDestructorsCompile.dfy

method Main()
{
}

method BaseKlef(k: Klef)
  requires !k.C0? && !k.C2? && !k.C1?
{
  var k' := k.(0 := 100, c3 := 200);
  assert k' == C3(k.3, 100, k.1, 200);
  print k', "\n";
}

method Matte(d: Datte<real>)
  requires !d.CC?
{
  var d := d;
  var s := d.(x := 5);
  print d, " ", s, "\n";
  d := BB(false, 12);
  s := d.(x := 6);
  print d, " ", s, "\n";
  d := CC(3.2);
  s := d.(c := 3.4);
  print d, " ", s, "\n";
  d := DD(100, {7}, 5, 9.0);
  s := d.(x := 30);
  print d, " ", s, "\n";
  s := s.(q := 2.0, p := d.p);
  print d, " ", s, "\n";
}

datatype Dt = A(x: int, y: real) | B(h: MyClass, x: int) | C(y: real)

class MyClass { }

datatype Klef = C0(0: int, 1: int, 2: int, c0: int) | C1(1: int, 2: int, 3: int, c1: int) | C2(2: int, 3: int, 0: int, c2: int) | C3(3: int, 0: int, 1: int, c3: int)

datatype Datte<T> = AA(a: int, x: int) | BB(b: bool, x: int) | CC(c: real) | DD(x: int, o: set<int>, p: bv27, q: T)
