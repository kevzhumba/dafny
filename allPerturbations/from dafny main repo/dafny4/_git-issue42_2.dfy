
// git-issue42.dfy

lemma L(x: int)
{
}

lemma {:warnShadowing false} L1(x: int)
{
  var x := 2;
}
