
// RlimitMultiplier.dfy

ghost function f(i: nat, j: nat): int
{
  if i == 0 then
    0
  else
    f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)
}

lemma {:timeLimitMultiplier 100} L()
{
}
