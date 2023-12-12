
// FindPivotIndex.dfy

function sum(nums: seq<int>): int
{
  if |nums| == 0 then
    0
  else
    sum(nums[0 .. |nums| - 1]) + nums[|nums| - 1]
}

function sumUp(nums: seq<int>): int
{
  if |nums| == 0 then
    0
  else
    nums[0] + sumUp(nums[1..])
}

lemma sumUpLemma(a: seq<int>, b: seq<int>)
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{
  if a == [] {
    assert a + b == b;
  } else {
    sumUpLemma(a[1..], b);
    calc {
      sumUp(a + b);
      {
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
      }
      a[0] + sumUp(a[1..] + b);
      a[0] + sumUp(a[1..]) + sumUp(b);
    }
  }
}

lemma sumsEqual(nums: seq<int>)
  ensures sum(nums) == sumUp(nums)
  decreases |nums|
{
  if nums == [] {
  } else {
    var ln := |nums| - 1;
    calc {
      sumUp(nums[..]);
      {
        assert nums[..] == nums[0 .. ln] + [nums[ln]];
        sumUpLemma(nums[0 .. ln], [nums[ln]]);
      }
      sumUp(nums[0 .. ln]) + sumUp([nums[ln]]);
      {
        assert forall a :: sumUp([a]) == a;
      }
      sumUp(nums[0 .. ln]) + nums[ln];
      {
        sumsEqual(nums[0 .. ln]);
      }
      sum(nums[0 .. ln]) + nums[ln];
    }
  }
}

method FindPivotIndex(nums: seq<int>) returns (index: int)
  requires |nums| > 0
  ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0 .. k]) != sum(nums[k + 1..])
  ensures 0 <= index < |nums| ==> sum(nums[0 .. index]) == sum(nums[index + 1..])
{
}
