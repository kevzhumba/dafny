
// git-issue42.dfy

lemma L(x: int)
{
  var x := 2;
}

lemma {:warnShadowing false} L1(x: int)
{
}
