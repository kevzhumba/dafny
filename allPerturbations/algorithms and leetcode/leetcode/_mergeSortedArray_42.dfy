
// mergeSortedArray.dfy

method swap(xs: array<int>, i: int, bs: array<int>, k: int)
  requires 0 <= i < xs.Length
  requires 0 <= k < bs.Length
  modifies xs, bs
  ensures xs[i] == old(bs[k]) && bs[k] == old(xs[i])
  ensures xs == bs ==> forall s :: 0 <= s < xs.Length && s != i && s != k ==> old(xs[s]) == xs[s]
  ensures xs != bs ==> forall s :: 0 <= s < xs.Length && s != i ==> old(xs[s]) == xs[s]
  ensures xs == bs ==> forall s :: 0 <= s < bs.Length && s != i && s != k ==> old(bs[s]) == bs[s]
  ensures xs != bs ==> forall s :: 0 <= s < bs.Length && s != k ==> old(bs[s]) == bs[s]
  ensures xs == bs ==> multiset(xs[..]) == multiset(old(xs[..]))
  ensures xs != bs ==> multiset(xs[..]) == multiset(old(xs[..])) - multiset{old(xs[i])} + multiset{old(bs[k])}
  ensures xs != bs ==> multiset(bs[..]) == multiset(old(bs[..])) - multiset{old(bs[k])} + multiset{old(xs[i])}
{
  xs[i], bs[k] := bs[k], xs[i];
}

predicate sortedArray(arry: array<int>)
  reads arry
{
  forall i, j :: 
    0 <= i < j < arry.Length ==>
      arry[i] <= arry[j]
}

predicate partialSortedArray(arry: array<int>, start: int, end: int)
  requires 0 <= start <= arry.Length
  requires 0 <= end <= arry.Length
  requires start <= end
  reads arry
{
  forall i, j :: 
    0 <= start <= i < j < end ==>
      arry[i] <= arry[j]
}

predicate partialSortedArrayUpper(arry: array<int>, start: int, end: int, bs: array<int>, a: int, b: int)
  requires 0 <= start <= arry.Length
  requires 0 <= end <= arry.Length
  requires 0 <= a <= start
  requires 0 <= b <= bs.Length
  requires b <= start
  requires start <= end
  reads arry, bs, arry
{
  partialSortedArray(arry, start, end) &&
  (start < arry.Length ==>
    forall k :: 
      0 <= k < a ==>
        arry[k] <= arry[start]) &&
  (start < arry.Length ==>
    forall k :: 
      0 <= k < b ==>
        bs[k] <= arry[start])
}

twostate lemma psaMaintained(arry: array<int>, start: int, end: int)
  requires 0 <= start < arry.Length
  requires 0 <= end < arry.Length
  requires start <= end
  requires old(partialSortedArray(arry, start, end + 1))
  requires old(arry[end]) != arry[end]
  requires forall i :: start <= i < end ==> arry[i] == old(arry[i])
  ensures partialSortedArray(arry, start, end)
{
}

twostate predicate arrayMultisetPreserved(xs: array<int>, ys: array<int>)
  reads xs, ys
{
  multiset(xs[..]) + multiset(ys[..]) == multiset(old(xs[..])) + multiset(old(ys[..]))
}

method Test()
{
  var toast := new int[3] [1, 2, 3];
  var gam := new int[3] [4, 5, 6];
  ghost var ms: multiset<int> := multiset(toast[..]) + multiset(gam[..]);
  assert toast[..] == [1, 2, 3];
  assert gam[..] == [4, 5, 6];
  assert ms == multiset([1, 2, 3]) + multiset([4, 5, 6]);
  label start:
  swap(toast, 1, gam, 1);
  assert toast[..] == [1, 5, 3];
  assert gam[1] == 2;
  assert gam[..] == [4, 2, 6];
  assert old@start(gam[..]) == [4, 5, 6];
  assert multiset(toast[..]) + multiset(gam[..]) == multiset(old@start(toast[..])) + multiset(old@start(gam[..]));
  swap(toast, 0, toast, 1);
  swap(toast, 0, gam, 2);
  assert ms == multiset(toast[..]) + multiset(gam[..]);
}

method merge(xs: array<int>, m: int, ys: array<int>, n: int)
  requires xs != ys
  requires 0 <= n
  requires n == ys.Length
  requires xs.Length == m + n
  requires 0 <= m < xs.Length
  requires forall i, j :: 0 <= i < j < m ==> xs[i] <= xs[j]
  requires forall j :: m <= j < m + n ==> xs[j] == 0
  requires sortedArray(ys)
  modifies xs, ys
  ensures arrayMultisetPreserved(xs, ys)
  ensures sortedArray(xs)
{
  var i := m + n - 1;
  var a := m - 1;
  var b := n - 1;
  while -1 <= i
    invariant -1 <= i < xs.Length
    invariant -1 <= a < m
    invariant -1 <= b < n <= ys.Length
    invariant i == a + b + 1
    invariant partialSortedArray(ys, 0, b + 1)
    invariant arrayMultisetPreserved(xs, ys)
    invariant partialSortedArray(xs, 0, a + 1)
    invariant partialSortedArrayUpper(xs, i + 1, m + n, ys, a + 1, b + 1)
  {
    label LS:
    if 0 <= a && 0 <= b {
      if xs[a] >= ys[b] {
        swap(xs, a, xs, i);
        a := a - 1;
      } else {
        swap(ys, b, xs, i);
        b := b - 1;
      }
    } else if 0 <= b {
      swap(ys, b, xs, i);
      b := b - 1;
    } else if 0 <= a {
      swap(xs, a, xs, i);
      a := a - 1;
    }
    i := i - 1;
  }
}
