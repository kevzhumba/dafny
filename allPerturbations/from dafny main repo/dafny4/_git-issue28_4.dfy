
// git-issue28.dfy

lemma mylemma()
{
  var shift: int := 1;
  assume (1 as bv32 << shift) as int == 2;
}
