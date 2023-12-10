
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet smallTest/sliceTest.dfy
// sliceTest.dfy

method MultipleReturns(x: int, y: int)
    returns (more: int, less: int, same: int)
  requires y > 0
  ensures less < x
  ensures x == same
  ensures x < more
{
  more := x + y;
  less := x - y;
  same := x;
}
