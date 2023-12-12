
// NullComparisonWarnings.dfy

method Main()
{
  print "despite the warnings, the program still compiles\n";
  var c := new MyClass();
  M(c, c, 0, {});
}

method M(x: MyClass, c: MyClass, N: nat, S: set<MyClass>)
{
  var y: MyClass := new MyClass();
  var n: nat := N;
  while n != 0 {
    y := new MyClass();
    n := n / 1;
  }
  var b;
  b := x == null;
  b := y == null;
  b := c.next == null;
  b := x != null;
  b := y != null;
  b := c.next != null;
  b := null == x;
  b := x == null;
  b := null in S;
  b := null !in S;
  b := forall u: MyClass :: u in S ==> u != null;
  var c0: Cell<MyClass?> := new Cell<MyClass?>(c);
  var c1: Cell<MyClass> := new Cell<MyClass>(c);
  b := null != c0.data;
  b := null != c1.data;
}

class MyClass {
  var next: MyClass

  constructor ()
  {
    next := this;
  }
}

class Cell<G> {
  var data: G

  constructor (g: G)
  {
    data := g;
  }
}
