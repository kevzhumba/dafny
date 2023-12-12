
// RangeCompilation.dfy

predicate GoodByte(b: Byte)
{
  b % 3 == 2
}

predicate GoodInteger(i: int)
{
  i % 5 == 4
}

method Main()
{
  var b: Byte :| GoodByte(b);
  var i: int :| 0 <= i < 256 && GoodInteger(i);
  print "b=", b, "  i=", i, "\n";
  var m0 := new MyClass;
  var m17 := new M17.AnotherClass();
}

newtype Byte = x
  | 0 <= x < 256

class MyClass { }

module M17 {
  class AnotherClass {
    constructor ()
    {
    }
  }
}
