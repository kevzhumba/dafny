
// EqualityTypesCompile.dfy

method M<A>(xs: List, a: A) returns (r: bool)
{
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
  var co := CoValue(3.14);
  var xs := Cons(co, Nil);
  var r;
  r := M(xs, co);
  print "from M: ", r, "\n";
  r := N((co, xs), co, Two(xs, xs));
  print "from N: ", r, "\n";
  r := H(co, co, 2.7, 2.7);
  print "from H: ", r, "\n";
}

datatype List<A> = Nil | Cons(A, List) | ICons(int, List)

datatype TwoLists<A> = Two(List, List)

codatatype Co<A> = Atom(A) | CoCons(int, Co) | CoConsA(A, Co)
