
// git-issue42.dfy

lemma L(x: int)
{
  var x := 3;
}

lemma {:warnShadowing false} L1(x: int)
{
  var x := 2;
}