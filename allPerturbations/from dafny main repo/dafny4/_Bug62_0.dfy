
// Bug62.dfy

class C {
  constructor C()
  {
  }

  method Main()
  {
  }
}

class D {
  method Main()
    modifies this
  {
    print "hello, I'm running ... in D\n";
  }
}

class E {
  static method Main()
    requires true
  {
    print "hello, I'm running ... in E\n";
  }
}
