
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet smallTest/smallTest.dfy
// smallTest.dfy

method Abs(x: int) returns (y: int)
  ensures 0 <= y
  decreases x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
