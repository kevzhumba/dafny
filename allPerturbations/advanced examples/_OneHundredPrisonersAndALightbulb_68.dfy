
// OneHundredPrisonersAndALightbulb.dfy

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
  decreases B
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  assert |B| == |B'| + 1;
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    assert A == B';
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
  decreases *
{
  count := 0;
  var I := {};
  var S := {};
  var switch := false;
  CardinalitySubsetLt(S, I);
  if I < P {
    CardinalitySubsetLt(I, P);
  }
  assert P <= I;
  assert I == P;
}
