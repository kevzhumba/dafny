
// relativeOrder.dfy

predicate IsEven(n: int)
{
  n % 2 == 0
}

method FindEvenNumbers(arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==> exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= |evenList| <= i
    invariant forall x :: x in arr[..i] && IsEven(x) ==> x in evenList[..]
    invariant forall x :: x !in arr[..i] ==> x !in evenList
    invariant |evenList| == |indices|
    invariant forall k :: 0 <= k < |indices| ==> indices[k] < i
    invariant forall k, l :: 0 <= k < l < |indices| ==> indices[k] < indices[l]
    invariant forall k :: 0 <= k < |evenList| ==> 0 <= indices[k] < i <= arr.Length && arr[indices[k]] == evenList[k]
    invariant forall k, l :: 0 <= k < l < |evenList| ==> exists n, m :: 0 <= n < m < i && evenList[k] == arr[n] && evenList[l] == arr[m]
  {
    if IsEven(arr[i]) {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
  }
  assert evenList == evenNumbers[..];
}
