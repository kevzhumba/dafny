
// Regression19.dfy

ghost predicate ContainsNothingBut5(s: set<int>)
{
  forall q :: 
    q in s ==>
      q == 5
}

ghost predicate YeahContains5(s: set<int>)
{
  exists q :: 
    q in s &&
    q == 5
}

ghost predicate ViaSetComprehension(s: set<int>)
{
  |set q | q in s && q == 5| != 0
}

ghost predicate LambdaTest(s: set<int>)
{
  (q => q in s)(5)
}

ghost predicate ViaMapComprehension(s: set<int>)
{
  |(map q | q in s && q == 5 :: true).Keys| != 0
}

ghost predicate Contains5(s: set<int>)
{
  var q := 5;
  q in s
}

ghost predicate RIs5(r: R)
{
  match r
  case MakeR(q) =>
    q == 5
  case Other =>
    false
}

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
{
}

lemma NonemptyMap(x: int, s: map<int, bool>)
  requires x in s.Keys
  ensures |s| != 0
{
}

method M(s: set<int>, r: R, q: int)
  requires s == {5} && r == MakeR(5)
{
}

datatype R = MakeR(int) | Other
