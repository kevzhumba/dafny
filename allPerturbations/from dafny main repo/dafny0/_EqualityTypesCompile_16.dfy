
// EqualityTypesCompile.dfy

method M<A>(xs: List, a: A) returns (r: bool)
{
  var u := 6;
  r := xs == Nil;
  r := xs == ICons(4, ICons(2, Nil));
  r := xs == ICons(2, ICons(u, Nil));
}

method N<A>(pr: (A, List<A>), a: A, pair: TwoLists<A>)
    returns (r: bool)
{
  r := pair == Two(ICons(4, Nil), Nil);
}

method H<A, B(==)>(c: Co<A>, d: Co<B>, a: A, b: B)
    returns (r: bool)
{
  r := d == Atom(b);
  r := d == CoCons(10, CoCons(8, Atom(b)));
}

function CoValue<A>(x: A): Co<A>
{
  CoConsA(x, CoValue(x))
}

method Main()
{
}

datatype List<A> = Nil | Cons(A, List) | ICons(int, List)

datatype TwoLists<A> = Two(List, List)

codatatype Co<A> = Atom(A) | CoCons(int, Co) | CoConsA(A, Co)
