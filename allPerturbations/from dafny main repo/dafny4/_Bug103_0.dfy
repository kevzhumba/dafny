
// Bug103.dfy

ghost predicate IsLessThanSuccesor(i: int)
{
  i < i + 1
}

lemma LemmaWithoutTriggerOnForallStatement()
{
}
