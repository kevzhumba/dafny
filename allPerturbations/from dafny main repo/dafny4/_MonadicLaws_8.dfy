
// MonadicLaws.dfy

ghost function append(xs: List, ys: List): List
{
  match xs
  case Nil =>
    ys
  case Cons(x, xs') =>
    Cons(x, append(xs', ys))
}

lemma AppendNil(xs: List)
  ensures append(xs, Nil) == xs
{
}

lemma AppendAssoc(xs: List, ys: List, zs: List)
  ensures append(append(xs, ys), zs) == append(xs, append(ys, zs))
{
}

ghost function Return<T>(a: T): List
{
  Cons(a, Nil)
}

ghost function Bind<T, U>(xs: List<T>, f: T -> List<U>): List<U>
{
  match xs
  case Nil =>
    Nil
  case Cons(x, xs') =>
    append(f(x), Bind(xs', f))
}

lemma LeftIdentity<T>(a: T, f: T -> List)
  ensures Bind(Return(a), f) == f(a)
{
  AppendNil(f(a));
}

lemma RightIdentity<T>(m: List)
  ensures Bind(m, Return) == m
{
  match m
  case {:split false} Nil =>
    assert Bind<T, T>(Nil, Return) == Nil;
  case {:split false} Cons(x, m') =>
    calc {
      Bind(Cons(x, m'), Return);
      append(Return(x), Bind(m', Return));
      Cons(x, Bind(m', Return));
    }
}

lemma Associativity<T>(m: List, f: T -> List, g: T -> List)
  ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
{
}

lemma BindOverAppend<T>(xs: List, ys: List, g: T -> List)
  ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
{
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(x, xs') =>
    AppendAssoc(g(x), Bind(xs', g), Bind(ys, g));
}

datatype List<T> = Nil | Cons(head: T, tail: List)
