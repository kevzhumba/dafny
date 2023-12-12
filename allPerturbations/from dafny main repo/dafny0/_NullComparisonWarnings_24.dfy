
// NullComparisonWarnings.dfy

method Main()
{
  print "despite the warnings, the program still compiles\n";
  var c := new MyClass();
  M(c, c, 0, {});
}

method M(x: MyClass, c: MyClass, N: nat, S: set<MyClass>)
{
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
