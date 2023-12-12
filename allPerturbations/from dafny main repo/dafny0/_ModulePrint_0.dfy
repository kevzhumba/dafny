
// ModulePrint.dfy

method Main()
{
  var c := new T.C();
  c.m();
}

abstract module S {
  class C {
    var f: int
    ghost var g: int
    var h: int

    method m()
      modifies this
  }
}

module T refines S {
  class C ... {
    ghost var h: int
    ghost var j: int
    var k: int

    constructor ()
    {
    }

    method m()
      ensures h == h
      ensures j == j
    {
    }
  }
}
