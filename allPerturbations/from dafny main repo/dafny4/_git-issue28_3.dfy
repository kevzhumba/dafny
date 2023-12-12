
// git-issue28.dfy

lemma mylemma()
{
  var shift: int := 1;
  assert (1 as bv32 << 1) as int == 2;
}
