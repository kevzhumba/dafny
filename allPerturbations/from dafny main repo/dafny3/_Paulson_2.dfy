
// Paulson.dfy

ghost function Apply<T>(f: FunctionHandle<T>, argument: T): T

ghost function After(f: FunctionHandle, g: FunctionHandle): FunctionHandle

lemma Definition_After<T>(f: FunctionHandle<T>, g: FunctionHandle<T>, arg: T)
  ensures Apply(After(f, g), arg) == Apply(f, Apply(g, arg))

ghost function Lmap(f: FunctionHandle, a: LList): LList
{
  match a
  case Nil =>
    Nil
  case Cons(x, xs) =>
    Cons(Apply(f, x), Lmap(f, xs))
}

ghost function Lappend(a: LList, b: LList): LList
{
  match a
  case Nil =>
    b
  case Cons(x, xs) =>
    Cons(x, Lappend(xs, b))
}

greatest lemma Example6(f: FunctionHandle, g: FunctionHandle, M: LList)
  ensures Lmap(After(f, g), M) == Lmap(f, Lmap(g, M))
{
}

ghost function Iterates<A>(f: FunctionHandle<LList<A>>, M: LList<A>): LList<LList<A>>
{
  Cons(M, Iterates(f, Apply(f, M)))
}

greatest lemma Eq24<A>(f: FunctionHandle<LList<A>>, M: LList<A>)
  ensures Lmap(f, Iterates(f, M)) == Iterates(f, Apply(f, M))
{
  calc {
    Lmap(f, Iterates(f, M));
    Lmap(f, Cons(M, Iterates(f, Apply(f, M))));
    Cons(Apply(f, M), Lmap(f, Iterates(f, Apply(f, M))));
  ==#[_k]
    calc {
      Lmap(f, Iterates(f, Apply(f, M)));
    ==#[_k - 1]
      {
        Eq24(f, Apply(f, M));
      }
      Iterates(f, Apply(f, Apply(f, M)));
    }
    Cons(Apply(f, M), Iterates(f, Apply(f, Apply(f, M))));
    Iterates(f, Apply(f, M));
  }
}

lemma CorollaryEq24<A>(f: FunctionHandle<LList<A>>, M: LList<A>)
  ensures Iterates(f, M) == Cons(M, Lmap(f, Iterates(f, M)))
{
  Eq24(f, M);
}

ghost function h<A>(f: FunctionHandle<LList<A>>, M: LList<A>): LList<LList<A>>

lemma Definition_h<A>(f: FunctionHandle<LList<A>>, M: LList<A>)
  ensures h(f, M) == Cons(M, Lmap(f, h(f, M)))

ghost function Iter<A>(n: nat, f: FunctionHandle<A>, arg: A): A
{
  if n == 0 then
    arg
  else
    Apply(f, Iter(n - 1, f, arg))
}

ghost function LmapIter(n: nat, f: FunctionHandle, arg: LList): LList
{
  if n == 0 then
    arg
  else
    Lmap(f, LmapIter(n - 1, f, arg))
}

lemma Lemma25<A>(n: nat, f: FunctionHandle<A>, b: A, M: LList<A>)
  ensures LmapIter(n, f, Cons(b, M)) == Cons(Iter(n, f, b), LmapIter(n, f, M))
{
}

lemma Lemma26<A>(n: nat, f: FunctionHandle, x: LList)
  ensures LmapIter(n, f, Lmap(f, x)) == LmapIter(n + 1, f, x)
{
}

greatest lemma BisimulationLemma<A>(n: nat, f: FunctionHandle<LList<A>>, u: LList<A>)
  ensures LmapIter(n, f, h(f, u)) == LmapIter(n, f, Iterates(f, u))
{
  calc {
    LmapIter(n, f, h(f, u));
    {
      Definition_h(f, u);
    }
    LmapIter(n, f, Cons(u, Lmap(f, h(f, u))));
    {
      Lemma25(n, f, u, Lmap(f, h(f, u)));
    }
    Cons(Iter(n, f, u), LmapIter(n, f, Lmap(f, h(f, u))));
    {
      Lemma26(n, f, h(f, u));
    }
    Cons(Iter(n, f, u), LmapIter(n + 1, f, h(f, u)));
  ==#[_k]
    calc {
      LmapIter(n + 1, f, h(f, u));
    ==#[_k - 1]
      LmapIter(n + 1, f, Iterates(f, u));
    }
    Cons(Iter(n, f, u), LmapIter(n + 1, f, Iterates(f, u)));
    {
      Lemma26(n, f, Iterates(f, u));
    }
    Cons(Iter(n, f, u), LmapIter(n, f, Lmap(f, Iterates(f, u))));
    {
      Lemma25(n, f, u, Lmap(f, Iterates(f, u)));
    }
    LmapIter(n, f, Cons(u, Lmap(f, Iterates(f, u))));
    {
      CorollaryEq24(f, u);
    }
    LmapIter(n, f, Iterates(f, u));
  }
}

lemma Example7<A>(f: FunctionHandle<LList<A>>)
  ensures forall M :: h(f, M) == Iterates(f, M)
{
  forall M | true {
    BisimulationLemma(0, f, M);
  }
}

greatest lemma Example8<A>(f: FunctionHandle<A>, M: LList<A>, N: LList<A>)
  ensures Lmap(f, Lappend(M, N)) == Lappend(Lmap(f, M), Lmap(f, N))
{
}

greatest lemma Associativity(a: LList, b: LList, c: LList)
  ensures Lappend(Lappend(a, b), c) == Lappend(a, Lappend(b, c))
{
}

codatatype LList<T> = Nil | Cons(head: T, tail: LList)

datatype FunctionHandle<T> = FH(T)
