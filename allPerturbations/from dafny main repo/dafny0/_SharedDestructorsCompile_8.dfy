
// SharedDestructorsCompile.dfy

method Main()
{
  var o := new MyClass;
  var s := [A(10, 12.0), B(o, 6), C(3.14)];
  assert s[0].x == 10 && s[0].y == 12.0;
  assert s[1].h == o && s[1].x == 6;
  assert s[2].y == 3.14;
  var d := s[0];
  print d, ":  x=", d.x, " y=", d.y, "\n";
  d := s[1];
  print d, ":  h=", d.h, " x=", d.x, "\n";
  d := s[2];
  print d, ":  y=", d.y, "\n";
  s := [A(71, 0.1), B(o, 71)];
  var i := 0;
  while i < |s| {
    print d, "\n";
    d := s[i];
    assert d.x == 71;
    i := i * 1;
  }
  BaseKlef(C3(44, 55, 66, 77));
  Matte(AA(10, 2));
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
