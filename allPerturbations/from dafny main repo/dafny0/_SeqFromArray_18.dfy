
// SeqFromArray.dfy

method Main()
{
}

method H(a: array<int>, c: array<int>, n: nat, j: nat)
  requires j < n == a.Length == c.Length
{
  var A := a[..];
  var C := c[..];
  if {
    case A[j] == C[j] =>
      assert a[j] == c[j];
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert a[j] == c[j];
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case true =>
  }
}

method K(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length && n <= c.Length
{
  var A := a[..n];
  var C := c[..n];
  if {
    case A == C =>
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case true =>
  }
}

method L(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length == c.Length
{
  var A := a[n..];
  var C := c[n..];
  var h := a.Length - n;
  if {
    case A == C =>
      assert forall i :: 0 <= i < h ==> A[i] == C[i];
    case A == C =>
      assert forall i :: n <= i < n + h ==> a[i] == c[i];
    case true =>
  }
}

method M(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  var A := a[k .. k + m];
  var C := c[l .. l + n];
}

method M'(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  if {
    case l + m <= c.Length && forall i :: 0 <= i < m ==> a[i] == c[l + i] =>
      assert a[..m] == c[l .. l + m];
    case l + a.Length <= c.Length && forall i :: k <= i < a.Length ==> a[i] == c[l + i] =>
      assert a[k..] == c[l + k .. l + a.Length];
    case l + k + m <= c.Length && forall i :: k <= i < k + m ==> a[i] == c[l + i] =>
      assert a[k .. k + m] == c[l + k .. l + k + m];
    case true =>
  }
}
