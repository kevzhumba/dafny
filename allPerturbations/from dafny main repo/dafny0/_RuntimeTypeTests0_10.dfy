
// RuntimeTypeTests0.dfy

method G()
{
  var s: set<int>;
  var t: set<nat>;
  s := {5, 7};
  t := s;
  s := t;
  print s, " and ", t, "\n";
}

method H()
{
  var c := new Class0;
  var a: Dt<Class0> := Atom(c, 10);
  var b: Dt<object>;
  b := a;
  print a, " and ", b, "\n";
}

method I()
{
  var c := new Class0;
  var a: Dt<Class0> := Atom(c, 10);
  var b: Dt<object>;
  b := a;
}

method J()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: set<Tr> := {c0, c1};
  var t: set<Class0> := {c0};
  s := t;
  print s, " and ", t, "\n";
}

method K()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: seq<Tr> := [c0, c1];
  var t: seq<Class0> := [c0];
  s := t;
  print s, " and ", t, "\n";
}

method L()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: multiset<Tr> := multiset{c0, c1};
  var t: multiset<Class0> := multiset{c0};
  s := t;
  print s, " and ", t, "\n";
}

method M()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: map<int, Tr> := map[8 := c0, 9 := c1];
  var t: map<int, Class0> := map[7 := c0];
  s := t;
  print s, " and ", t, "\n";
}

method Downcast()
{
  var c0 := new Class0;
  var s: seq<Class0> := [c0, c0];
  var t: seq<Tr> := s;
  t := s;
  print s, " and ", t, "\n";
}

method Main()
{
  G();
  H();
  I();
  J();
  K();
  L();
  M();
  Downcast();
}

trait Tr {
  var u: char
}

class Class0 extends Tr {
  var x: int
}

class Class1 extends Tr {
  var y: real
}

datatype Dt<+A> = Atom(get: A, more: int)
