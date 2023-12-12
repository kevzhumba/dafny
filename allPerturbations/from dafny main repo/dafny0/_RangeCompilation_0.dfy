
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
