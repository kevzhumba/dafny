
// Streams.dfy

ghost function append(M: Stream, N: Stream): Stream
{
  match M
  case Nil =>
    N
  case Cons(t, M') =>
    Cons(t, append(M', N))
}

ghost function f(x: X): X

ghost function g(x: X): X

ghost function map_f(M: Stream<X>): Stream<X>
{
  match M
  case Nil =>
    Nil
  case Cons(x, N) =>
    Cons(f(x), map_f(N))
}

ghost function map_g(M: Stream<X>): Stream<X>
{
  match M
  case Nil =>
    Nil
  case Cons(x, N) =>
    Cons(g(x), map_g(N))
}

ghost function map_fg(M: Stream<X>): Stream<X>
{
  match M
  case Nil =>
    Nil
  case Cons(x, N) =>
    Cons(f(g(x)), map_fg(N))
}

greatest lemma Theorem0(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M))
{
  match M {
    case {:split false} Nil =>
    case {:split false} Cons(x, N) =>
      Theorem0(N);
  }
}

greatest lemma Theorem0_Alt(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M))
{
  if M.Cons? {
    Theorem0_Alt(M.tail);
  }
}

lemma Theorem0_Par(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M))
{
  forall k: nat | true {
    Theorem0_Ind(k, M);
  }
}

lemma Theorem0_Ind(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M))
{
  if k != 0 {
    match M {
      case {:split false} Nil =>
      case {:split false} Cons(x, N) =>
        Theorem0_Ind(k - 1, N);
    }
  }
}

lemma Theorem0_AutoInd(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M))
{
}

greatest lemma Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N))
{
  match M {
    case {:split false} Nil =>
    case {:split false} Cons(x, M') =>
      Theorem1(M', N);
  }
}

greatest lemma Theorem1_Alt(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N))
{
  if M.Cons? {
    Theorem1_Alt(M.tail, N);
  }
}

lemma Theorem1_Par(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N))
{
  forall k: nat | true {
    Theorem1_Ind(k, M, N);
  }
}

lemma Theorem1_Ind(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N))
{
  match M {
    case {:split false} Nil =>
    case {:split false} Cons(x, M') =>
      if k != 0 {
        Theorem1_Ind(k - 1, M', N);
      }
  }
}

lemma Theorem1_AutoInd(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N))
{
}

lemma Theorem1_AutoForall()
{
}

lemma Theorem2(M: Stream<X>)
  ensures append(Nil, M) == M
{
}

greatest lemma Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M
{
  match M {
    case {:split false} Nil =>
    case {:split false} Cons(x, N) =>
      Theorem3(N);
  }
}

greatest lemma Theorem3_Alt(M: Stream<X>)
  ensures append(M, Nil) == M
{
  if M.Cons? {
    Theorem3_Alt(M.tail);
  }
}

greatest lemma Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P)
{
  match M {
    case {:split false} Nil =>
    case {:split false} Cons(x, M') =>
      Theorem4(M', N, P);
  }
}

greatest lemma Theorem4_Alt(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P)
{
  if M.Cons? {
    Theorem4_Alt(M.tail, N, P);
  }
}

ghost function FlattenStartMarker<T>(M: Stream<Stream>, startMarker: T): Stream
{
  PrependThenFlattenStartMarker(Nil, M, startMarker)
}

ghost function PrependThenFlattenStartMarker<T>(prefix: Stream, M: Stream<Stream>, startMarker: T): Stream
{
  match prefix
  case Cons(hd, tl) =>
    Cons(hd, PrependThenFlattenStartMarker(tl, M, startMarker))
  case Nil =>
    match M
    case Nil =>
      Nil
    case Cons(s, N) =>
      Cons(startMarker, PrependThenFlattenStartMarker(s, N, startMarker))
}

greatest predicate StreamOfNonEmpties(M: Stream<Stream>)
{
  match M
  case Nil =>
    true
  case Cons(s, N) =>
    s.Cons? &&
    StreamOfNonEmpties(N)
}

ghost function FlattenNonEmpties(M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M)
{
  PrependThenFlattenNonEmpties(Nil, M)
}

ghost function PrependThenFlattenNonEmpties(prefix: Stream, M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M)
{
  match prefix
  case Cons(hd, tl) =>
    Cons(hd, PrependThenFlattenNonEmpties(tl, M))
  case Nil =>
    match M
    case Nil =>
      Nil
    case Cons(s, N) =>
      Cons(s.head, PrependThenFlattenNonEmpties(s.tail, N))
}

ghost function Prepend<T>(x: T, M: Stream<Stream>): Stream<Stream>
{
  match M
  case Nil =>
    Nil
  case Cons(s, N) =>
    Cons(Cons(x, s), Prepend(x, N))
}

greatest lemma Prepend_Lemma<T>(x: T, M: Stream<Stream>)
  ensures StreamOfNonEmpties(Prepend(x, M))
{
  match M {
    case {:split false} Nil =>
    case {:split false} Cons(s, N) =>
      Prepend_Lemma(x, N);
  }
}

lemma Theorem_Flatten<T>(M: Stream<Stream>, startMarker: T)
  ensures StreamOfNonEmpties(Prepend(startMarker, M)) ==> FlattenStartMarker(M, startMarker) == FlattenNonEmpties(Prepend(startMarker, M))
{
  Prepend_Lemma(startMarker, M);
  Lemma_Flatten(Nil, M, startMarker);
}

greatest lemma Lemma_Flatten<T>(prefix: Stream, M: Stream<Stream>, startMarker: T)
  ensures StreamOfNonEmpties(Prepend(startMarker, M)) ==> PrependThenFlattenStartMarker(prefix, M, startMarker) == PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M))
{
  Prepend_Lemma(startMarker, M);
  match prefix {
    case {:split false} Cons(hd, tl) =>
      Lemma_Flatten(tl, M, startMarker);
    case {:split false} Nil =>
      match M {
        case {:split false} Nil =>
        case {:split false} Cons(s, N) =>
          if * {
            Lemma_Flatten(s, N, startMarker);
          } else {
            calc {
              PrependThenFlattenStartMarker(prefix, M, startMarker);
            ==
              Cons(startMarker, PrependThenFlattenStartMarker(s, N, startMarker));
            }
            calc {
              PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M));
            ==
              PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, Cons(s, N)));
            ==
              PrependThenFlattenNonEmpties(prefix, Cons(Cons(startMarker, s), Prepend(startMarker, N)));
            ==
              Cons(Cons(startMarker, s).head, PrependThenFlattenNonEmpties(Cons(startMarker, s).tail, Prepend(startMarker, N)));
            ==
              Cons(startMarker, PrependThenFlattenNonEmpties(s, Prepend(startMarker, N)));
            }
          }
      }
  }
}

greatest lemma Lemma_FlattenAppend0<T>(s: Stream, M: Stream<Stream>, startMarker: T)
  ensures PrependThenFlattenStartMarker(s, M, startMarker) == append(s, PrependThenFlattenStartMarker(Nil, M, startMarker))
{
  match s {
    case {:split false} Nil =>
    case {:split false} Cons(hd, tl) =>
      Lemma_FlattenAppend0(tl, M, startMarker);
  }
}

greatest lemma Lemma_FlattenAppend1<T>(s: Stream, M: Stream<Stream>)
  requires StreamOfNonEmpties(M)
  ensures PrependThenFlattenNonEmpties(s, M) == append(s, PrependThenFlattenNonEmpties(Nil, M))
{
  match s {
    case {:split false} Nil =>
    case {:split false} Cons(hd, tl) =>
      Lemma_FlattenAppend1(tl, M);
  }
}

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

type X(!new)
