
// ContainerRanks.dfy

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
}

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
}

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
}

datatype Abc = End | Wrapper(seq<Abc>)

datatype Def = End | MultiWrapper(multiset<Def>)

datatype Ghi = End | SetWrapper(set<Ghi>)
