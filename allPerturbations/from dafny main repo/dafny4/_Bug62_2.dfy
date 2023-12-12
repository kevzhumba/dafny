
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
    print "hello, I'm running ... in D\n";
  }
}

class E {
  static method Main()
    requires true
  {
  }
}
