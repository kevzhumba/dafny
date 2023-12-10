
// validAnagram.dfy

method toMultiset(s: string) returns (mset: multiset<char>)
  ensures multiset(s) == mset
{
  mset := multiset{};
  for i := 0 to |s|
    invariant mset == multiset(s[0 .. i])
  {
    assert s == s[0 .. i] + [s[i]] + s[i + 1..];
    mset := mset + multiset{s[i]};
  }
  assert s == s[0 .. |s|];
  return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
  ensures s == t <==> equal
{
}

method isAnagram(s: string, t: string) returns (equal: bool)
  ensures (multiset(s) == multiset(t)) == equal
{
  var smset := toMultiset(s);
  var tmset := toMultiset(t);
  equal := msetEqual(smset, tmset);
}
