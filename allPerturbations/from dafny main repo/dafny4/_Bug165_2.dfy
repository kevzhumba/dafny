
// Bug165.dfy

ghost function f(a: T): bool

method Select(s1: seq<T>) returns (r: seq<T>)
  ensures forall e: T :: f(e) ==> multiset(s1)[e] == multiset(r)[e]
  ensures forall e: T :: !f(e) ==> 0 == multiset(r)[e]

method Main(s1: seq<T>)
{
  var r1, r2: seq<T>;
  r1 := Select(s1);
  assert multiset(r1) == multiset(r2);
}

type T(!new)
