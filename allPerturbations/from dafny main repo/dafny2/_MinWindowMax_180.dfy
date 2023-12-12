
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
  var b := new int[a.Length];
  b[0] := 0;
  var k, l := 0, 1;
  var n := 1;
  while n < W
    invariant 0 <= k < l <= n <= W
    invariant StrictlyIncreasing(b, k, l, 0, n)
    invariant RightmostMax(a, 0, b[k], n)
    invariant forall u :: k < u < l ==> RightmostMax(a, b[u - 1] + 1, b[u], n)
    invariant b[l - 1] == n - 1
    invariant l - k <= W
  {
    while k <= l - 1 && a[b[l - 1]] <= a[n]
      invariant k <= l <= n
      invariant forall i :: (if k < l then b[l - 1] + 1 else 0) <= i < n ==> a[i] <= a[n]
    {
      l := l - 1;
    }
    b[l], l := n, l + 1;
    n := n + 1;
  }
  m := a[b[k]];
  Maxes(a, 0, b[k], n);
  start := 0;
  while n < a.Length
    invariant 0 <= k < l <= n <= a.Length
    invariant StrictlyIncreasing(b, k, l, n - W, n)
    invariant RightmostMax(a, n - W, b[k], n)
    invariant forall u :: k < u < l ==> RightmostMax(a, b[u - 1] + 1, b[u], n)
    invariant b[l - 1] == n - 1
    invariant 0 <= start <= a.Length - W
    invariant m == Max(a, start, W)
    invariant forall s :: 0 <= s <= n - W ==> m <= Max(a, s, W)
    invariant l - k <= W
  {
    while k <= l - 1 && a[b[l - 1]] <= a[n]
      invariant k <= l <= n
      invariant forall i :: (if k < l then b[l - 1] + 1 else n - W) <= i < n ==> a[i] <= a[n]
    {
      l := l - 1;
    }
    b[l], l := n, l + 1;
    if k < l - 1 && b[k] == n - W {
      k := k + 1;
    }
    Maxes(a, n - W + 1, b[k], n + 1);
    if a[b[k]] < m {
      m, start := a[b[k]], n - W + 1;
    }
    n := n + 1;
    Bound(b, k, l, n, W);
  }
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
  }
}
