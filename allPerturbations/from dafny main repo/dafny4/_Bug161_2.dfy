
// Bug161.dfy

ghost predicate P(x: t)

ghost function F(x: t): int

ghost function C(): int
{
  assume exists x :: P(x);
  var x :| P(x);
  F(x)
}

lemma L(x: t)
{
  assume P(x);
  assert F(x) == C();
}

type t = seq<int>
