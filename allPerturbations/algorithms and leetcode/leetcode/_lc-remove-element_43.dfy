
// lc-remove-element.dfy

method removeElement(nums: array<int>, val: int) returns (i: int)
  modifies nums
  ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
{
}

method Main()
{
  var elems := new int[5] [1, 2, 3, 4, 5];
  var res := removeElement(elems, 5);
  print res, "\n", elems;
}
