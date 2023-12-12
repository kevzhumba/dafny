
// Bug165.dfy

ghost function f(a: T): bool

method Select(s1: seq<T>) returns (r: seq<T>)
  ensures forall e: T :: f(e) ==> multiset(s1)[e] == multiset(r)[e]
  ensures forall e: T :: !f(e) ==> 0 == multiset(r)[e]

method Main(s1: seq<T>)
{
}

type T(!new)
