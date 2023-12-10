method Nine(i: int) returns (j: int)
  requires i >= 0
  ensures j == i
{
  if i == 0 {
    j := i;
  } else {
    var k := 1;
    j := k;
  }
}
