
// sliceTest.dfy

method MultipleReturns(x: int, y: int)
    returns (more: int, less: int, same: int)
  requires y > 0
  ensures less < x
  ensures x == same
  ensures x < more
{
  more := x + y;
}
