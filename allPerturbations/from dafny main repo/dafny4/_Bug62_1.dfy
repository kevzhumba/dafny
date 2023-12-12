
// Bug62.dfy

class C {
  constructor C()
  {
  }

  method Main()
  {
    print "hello, I'm running ... in C\n";
  }
}

class D {
  method Main()
    modifies this
  {
  }
}

class E {
  static method Main()
    requires true
  {
    print "hello, I'm running ... in E\n";
  }
}
