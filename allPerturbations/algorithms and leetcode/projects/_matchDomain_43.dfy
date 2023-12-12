include "../lib/seq.dfy"
// matchDomain.dfy

ghost predicate TokensEqual<T(==)>(left: seq<T>, right: seq<T>)
{
  |left| == |right| &&
  forall i: nat :: 
    i < |left| ==>
      left[i] == right[i]
}

lemma PrefixesEqual<T(==)>(left: seq<T>, right: seq<T>)
  requires TokensEqual(reverse(left), reverse(right))
  ensures TokensEqual(left, right)
{
  ReverseIndexAll(left);
  ReverseIndexAll(right);
  assert |left| == |reverse(left)|;
  assert |right| == |reverse(right)|;
  forall i: nat | i < |left|
    ensures left[i] == right[i]
  {
    ReverseIndexBack(left, i);
    ReverseIndexBack(right, i);
  }
}

method matchDomain(domain: seq<Token>, allowedDomain: seq<Token>) returns (allowed: bool)
  requires forall i: nat :: i < |domain| ==> domain[i] != Wildcard
  requires Wildcard in allowedDomain ==> |allowedDomain| > 1 && allowedDomain[0] == Wildcard && forall i: nat :: 0 < i < |allowedDomain| ==> allowedDomain[i] != Wildcard
  ensures allowed <==> TokensEqual(domain, allowedDomain) || (Wildcard in allowedDomain && IsSuffix(allowedDomain[1..], domain) && |domain| >= |allowedDomain|)
{
  var splitDomain := reverse(domain);
  var splitAllowedDomain := reverse(allowedDomain);
  ReverseIndexAll(allowedDomain);
  ReverseIndexAll(domain);
  if |domain| < |allowedDomain| {
    return false;
  }
  var i := 0;
  while i < |allowedDomain|
    invariant 0 <= i <= |allowedDomain|
    invariant IsPrefix(splitAllowedDomain[..i], splitDomain)
    invariant Wildcard !in splitAllowedDomain[..i]
  {
    if splitAllowedDomain[i] == Wildcard {
      reverseInitList(allowedDomain);
      assert reverse(splitAllowedDomain[..|splitAllowedDomain| - 1]) == allowedDomain[1..];
      IsPrefixReversed(splitAllowedDomain[..i], splitDomain);
      reverseReverseIdempotent(domain);
      return true;
    }
    if splitDomain[i] != splitAllowedDomain[i] {
      return false;
    }
    i := i + 1;
  }
  assert Wildcard !in splitAllowedDomain;
  if i > |domain| {
    assert |allowedDomain| <= |domain|;
    return false;
  }
  PrefixesEqual(allowedDomain, domain);
  return true;
}

method Test()
{
  var domain := [Token("chat"), Token("help"), Token("dell"), Token("com")];
  var suf := [Token("dell"), Token("com")];
  var wild := [Wildcard, Token("dell"), Token("com")];
  assert IsSuffix(suf, domain);
  var test1 := matchDomain(suf, wild);
}

import opened Seq

datatype Token = Token(val: string) | Wildcard
