
// Regression7.dfy

method Main()
{
  var q := Q.FQ(ListLibrary.Nil, ListLibrary.Nil);
  var x := 28.0;
  var ll := Q.Test(q, x);
  print ll, "\n";
}

module ListLibrary {
  datatype List<B> = Nil | Cons(head: B, tail: List<B>)
}

module Q {
  function MyCons<W>(w: W, ws: LL.List<W>): LL.List<W>
  {
    LL.Cons(w, ws)
  }

  method Test<A>(q: Queue<A>, x: A) returns (r: LL.List<A>)
  {
  }

  import LL = ListLibrary

  datatype Queue<T> = FQ(front: LL.List<T>, rear: LL.List<T>)
}
