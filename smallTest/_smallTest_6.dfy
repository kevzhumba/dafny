
// smallTest.dfy

method Abs(x: int) returns (y: int)
  ensures 0 <= y
  decreases x
{
  if x < -1 {
    return -x;
  } else {
    return x;
  }
}
