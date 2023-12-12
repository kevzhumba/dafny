
// bubblesort.dfy

function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

function SumRange(lo: int, hi: int): int
  decreases hi - lo
{
  if lo >= hi then
    0
  else
    SumRange(lo, hi - 1) + hi - 1
}

lemma SumRangeNChoose2(n: nat)
  ensures SumRange(0, n) == NChoose2(n)
{
}

lemma SumRangeUnrollLeft(lo: int, hi: int)
  ensures SumRange(lo, hi) == if lo >= hi then 0 else lo + SumRange(lo + 1, hi)
  decreases hi - lo
{
}

method BubbleSort(a: array<int>) returns (n: nat)
  modifies a
  ensures n <= NChoose2(a.Length)
{
}
