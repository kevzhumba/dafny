
// Array2dAs1d.dfy

lemma lemma_mul_le(x: int, y: int, z: int)
  requires 0 <= z
  requires x <= y
  ensures x * z <= y * z
{
}

method foo(input: array<int>, rows: int, cols: int)
  requires input != null
  requires rows > 0 && cols > 0
  requires rows * cols == input.Length
{
  var i := 0;
  while i < rows {
    var j := 0;
    i := i + 1;
  }
}
