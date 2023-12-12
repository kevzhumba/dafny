
// git-issue155.dfy

ghost function F(a: A, b: B): int
{
  match (a, b)
  case (A0, B0) =>
    0
}

method M(a: A, b: B)
{
  match (a, b)
  case {:split false} (A0, B0) =>
}

datatype A = A0

datatype B = B0
