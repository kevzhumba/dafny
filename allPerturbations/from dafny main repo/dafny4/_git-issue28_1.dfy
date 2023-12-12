
// git-issue28.dfy

lemma mylemma()
{
  var shift: int := 0;
  assume (1 as bv32 << shift) as int == 2;
  assert (1 as bv32 << 1) as int == 2;
}
