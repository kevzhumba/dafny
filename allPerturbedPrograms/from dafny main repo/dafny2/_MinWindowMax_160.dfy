
// MinWindowMax.dfy

method Main()
{
  var a := new [] [2, 3, -5, 2, 3];
  var m, start := MinimumWindowMax(a, 1);
  print "Window size 1:  min window-max is ", m, "\n";
  m, start := MinimumWindowMax(a, 2);
  print "Window size 2:  min window-max is ", m, "\n";
  m, start := MinimumWindowMax(a, 3);
  print "Window size 3:  min window-max is ", m, "\n";
  m, start := MinimumWindowMax(a, 5);
  print "Window size 5:  min window-max is ", m, "\n";
}

method MinimumWindowMax(a: array<int>, W: int)
    returns (m: int, start: int)
  requires 1 <= W <= a.Length
  ensures 0 <= start <= a.Length - W
  ensures m == Max(a, start, W)
  ensures forall s :: 0 <= s <= a.Length - W ==> m <= Max(a, s, W)
{
}

ghost function Max(a: array<int>, s: int, len: int): int
  requires 0 <= s && 1 <= len && s + len <= a.Length
  reads a
{
  if len == 1 then
    a[s]
  else
    var m := Max(a, s, len - 1); var y := a[s + len - 1]; if y < m then m else y
}

lemma MaxProperty(a: array<int>, s: int, len: int)
  requires 0 <= s && 1 <= len && s + len <= a.Length
  ensures forall i :: s <= i < s + len ==> a[i] <= Max(a, s, len)
  ensures exists i :: s <= i < s + len && a[i] == Max(a, s, len)
{
  if len == 1 {
    assert a[s] == Max(a, s, len);
  } else {
    MaxProperty(a, s, len - 1);
  }
}

ghost predicate RightmostMax(a: array<int>, lo: int, x: int, hi: int)
  requires 0 <= lo <= x < hi <= a.Length
  reads a
{
  (forall i :: 
    lo <= i < x ==>
      a[i] <= a[x]) &&
  forall i :: 
    x < i < hi ==>
      a[i] < a[x]
}

lemma Maxes(a: array<int>, lo: int, x: int, hi: int)
  requires 0 <= lo <= x < hi <= a.Length
  requires RightmostMax(a, lo, x, hi)
  ensures a[x] == Max(a, lo, hi - lo)
{
  MaxProperty(a, lo, hi - lo);
}

ghost predicate StrictlyIncreasing(b: array<int>, k: int, l: int, lo: int, hi: int)
  requires 0 <= k <= l <= b.Length
  reads b
{
  (forall i :: 
    k <= i < l ==>
      lo <= b[i] < hi) &&
  forall i, j :: 
    k <= i < j < l ==>
      b[i] < b[j]
}

lemma Bound(b: array<int>, k: int, l: int, n: int, W: nat)
  requires 0 <= k <= l <= b.Length
  requires forall i :: k <= i < l ==> n - W <= b[i] < n
  requires forall i, j :: k <= i < j < l ==> b[i] < b[j]
  ensures l - k <= W
  decreases W
{
  if k < l {
    assert n - W <= b[k] < n;
    Bound(b, k + 1, l, n, W - 1);
  }
}
