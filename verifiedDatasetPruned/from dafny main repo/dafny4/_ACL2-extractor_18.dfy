
// ACL2-extractor.dfy

ghost function length(xs: List): nat
{
  match xs
  case Nil =>
    0
  case Cons(_ /* _v0 */, rest) =>
    1 + length(rest)
}

opaque ghost function nth<T(00)>(n: int, xs: List<T>): T
{
  if 0 <= n < length(xs) then
    nthWorker(n, xs)
  else
    var t :| true; t
}

ghost function nthWorker<T>(n: int, xs: List<T>): T
  requires 0 <= n < length(xs)
{
  if n == 0 then
    xs.head
  else
    nthWorker(n - 1, xs.tail)
}

ghost function append(xs: List, ys: List): List
{
  match xs
  case Nil =>
    ys
  case Cons(x, rest) =>
    Cons(x, append(rest, ys))
}

ghost function rev(xs: List): List
{
  match xs
  case Nil =>
    Nil
  case Cons(x, rest) =>
    append(rev(rest), Cons(x, Nil))
}

ghost function nats(n: nat): List<int>
{
  if n == 0 then
    Nil
  else
    Cons(n - 1, nats(n - 1))
}

ghost function xtr<T(00)>(mp: List<int>, lst: List): List
{
  match mp
  case Nil =>
    Nil
  case Cons(n, rest) =>
    Cons(nth(n, lst), xtr(rest, lst))
}

lemma ExtractorTheorem<T(00)>(xs: List)
  ensures xtr(nats(length(xs)), xs) == rev(xs)
{
  var a, b := xtr(nats(length(xs)), xs), rev(xs);
  calc {
    length(a);
    {
      XtrLength(nats(length(xs)), xs);
    }
    length(nats(length(xs)));
    {
      NatsLength(length(xs));
    }
    length(xs);
  }
  calc {
    length(xs);
    {
      RevLength(xs);
    }
    length(b);
  }
  forall i | 0 <= i < length(xs)
    ensures nth(i, a) == nth(i, b)
  {
    reveal nth();
    ExtractorLemma(i, xs);
  }
  EqualElementsMakeEqualLists(a, b);
}

lemma XtrLength(mp: List<int>, lst: List)
  ensures length(xtr(mp, lst)) == length(mp)
{
}

lemma NatsLength(n: nat)
  ensures length(nats(n)) == n
{
}

lemma AppendLength(xs: List, ys: List)
  ensures length(append(xs, ys)) == length(xs) + length(ys)
{
}

lemma RevLength(xs: List)
  ensures length(rev(xs)) == length(xs)
{
  match xs {
    case {:split false} Nil =>
    case {:split false} Cons(x, rest) =>
      calc {
        length(append(rev(rest), Cons(x, Nil)));
        {
          AppendLength(rev(rest), Cons(x, Nil));
        }
        length(rev(rest)) + length(Cons(x, Nil));
        length(rev(rest)) + 1;
      }
  }
}

lemma EqualElementsMakeEqualLists<T(00)>(xs: List, ys: List)
  requires length(xs) == length(ys)
  requires forall i :: 0 <= i < length(xs) ==> nth(i, xs) == nth(i, ys)
  ensures xs == ys
{
  reveal nth();
  match xs {
    case {:split false} Nil =>
    case {:split false} Cons(x, rest) =>
      assert nth(0, xs) == nth(0, ys);
      forall i | 0 <= i < length(xs.tail) {
        calc {
          nth(i, xs.tail) == nth(i, ys.tail);
          nth(i + 1, Cons(xs.head, xs.tail)) == nth(i + 1, Cons(ys.head, ys.tail));
          nth(i + 1, xs) == nth(i + 1, ys);
        }
      }
  }
}

lemma {:vcs_split_on_every_assert} ExtractorLemma<T(00)>(i: int, xs: List)
  requires 0 <= i < length(xs)
  ensures nth(i, xtr(nats(length(xs)), xs)) == nth(i, rev(xs))
{
  calc {
    nth(i, xtr(nats(length(xs)), xs));
    {
      NatsLength(length(xs));
      NthXtr(i, nats(length(xs)), xs);
    }
    nth(nth(i, nats(length(xs))), xs);
    {
      NthNats(i, length(xs));
    }
    nth(length(xs) - 1 - i, xs);
    {
      reveal nth();
      RevLength(xs);
      NthRev(i, xs);
    }
    nth(i, rev(xs));
  }
}

lemma NthXtr<T(00)>(i: int, mp: List<int>, lst: List<T>)
  requires 0 <= i < length(mp)
  ensures nth(i, xtr(mp, lst)) == nth(nth(i, mp), lst)
{
  reveal nth();
  XtrLength(mp, lst);
  assert nth(i, xtr(mp, lst)) == nthWorker(i, xtr(mp, lst));
  if i == 0 {
  } else {
  }
}

lemma NthNats(i: int, n: nat)
  requires 0 <= i < n
  ensures nth(i, nats(n)) == n - 1 - i
{
  reveal nth();
  NatsLength(n);
  NthNatsWorker(i, n);
}

lemma NthNatsWorker(i: int, n: nat)
  requires 0 <= i < n && length(nats(n)) == n
  ensures nthWorker(i, nats(n)) == n - 1 - i
{
}

lemma NthRev<T(00)>(i: int, xs: List)
  requires 0 <= i < length(xs) == length(rev(xs))
  ensures nthWorker(i, rev(xs)) == nthWorker(length(xs) - 1 - i, xs)
{
  reveal nth();
  assert xs.Cons?;
  assert 1 <= length(rev(xs)) && rev(xs).Cons?;
  RevLength(xs.tail);
  if i < length(rev(xs.tail)) {
    calc {
      nth(i, rev(xs));
      nthWorker(i, rev(xs));
      nthWorker(i, append(rev(xs.tail), Cons(xs.head, Nil)));
      {
        NthAppendA(i, rev(xs.tail), Cons(xs.head, Nil));
      }
      nthWorker(i, rev(xs.tail));
      {
        NthRev(i, xs.tail);
      }
      nthWorker(length(xs.tail) - 1 - i, xs.tail);
      nthWorker(length(xs.tail) - 1 - i + 1, xs);
      nthWorker(length(xs) - 1 - i, xs);
    }
  } else {
    assert i == length(rev(xs.tail));
    calc {
      nth(i, rev(xs));
      nthWorker(i, rev(xs));
      nthWorker(i, append(rev(xs.tail), Cons(xs.head, Nil)));
      {
        NthAppendB(i, rev(xs.tail), Cons(xs.head, Nil));
      }
      nthWorker(i - length(rev(xs.tail)), Cons(xs.head, Nil));
      nthWorker(0, Cons(xs.head, Nil));
      nthWorker(0, xs);
      nthWorker(length(xs) - 1 - length(xs.tail), xs);
      {
        RevLength(xs.tail);
      }
      nthWorker(length(xs) - 1 - length(rev(xs.tail)), xs);
      nth(length(xs) - 1 - length(rev(xs.tail)), xs);
      nth(length(xs) - 1 - i, xs);
    }
  }
}

lemma NthAppendA<T(00)>(i: int, xs: List, ys: List)
  requires 0 <= i < length(xs)
  ensures nth(i, append(xs, ys)) == nth(i, xs)
{
  reveal nth();
  if i == 0 {
    calc {
      nth(0, append(xs, ys));
      nth(0, Cons(xs.head, append(xs.tail, ys)));
      xs.head;
    }
  } else {
    calc {
      nth(i, append(xs, ys));
      nth(i, Cons(xs.head, append(xs.tail, ys)));
      nth(i - 1, append(xs.tail, ys));
      {
        NthAppendA(i - 1, xs.tail, ys);
      }
      nth(i - 1, xs.tail);
    }
  }
}

lemma NthAppendB<T(00)>(i: int, xs: List, ys: List)
  requires length(xs) <= i < length(xs) + length(ys)
  ensures nth(i, append(xs, ys)) == nth(i - length(xs), ys)
{
  reveal nth();
  AppendLength(xs, ys);
  match xs {
    case {:split false} Nil =>
      assert nth(i, append(xs, ys)) == nth(i, ys);
    case {:split false} Cons(x, rest) =>
      calc {
        nth(i, append(xs, ys));
        nth(i, append(Cons(x, rest), ys));
        nth(i, Cons(x, append(rest, ys)));
        nth(i - 1, append(rest, ys));
        {
          NthAppendB(i - 1, rest, ys);
        }
        nth(i - 1 - length(rest), ys);
      }
  }
}

datatype List<T> = Nil | Cons(head: T, tail: List)
