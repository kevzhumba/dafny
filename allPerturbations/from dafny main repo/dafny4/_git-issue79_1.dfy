
// git-issue79.dfy

ghost function Inc(p: Pair): Pair
{
  match p
  case (s, Int(x)) =>
    (s, Int(x + 1))
  case (s, Unknown) =>
    (s, Unknown)
}

ghost function Inc2(s1: string, t1: EInt): Pair
{
  match (s1, t1)
  case (s1, Int(x)) =>
    (s1, Int(x + 1))
  case (s1, Unknown) =>
    (s1, Unknown)
}

ghost function Inc3(s1: string, t1: EInt, t2: EInt): Pair
{
  match (s1, t1, t2)
  case (s1, Int(x), Unknown) =>
    (s1, Int(x + 1))
  case (s1, Int(x), Int(y)) =>
    (s1, Int(x + y + 1))
  case (s1, Unknown, Unknown) =>
    (s1, Unknown)
  case (s1, Unknown, Int(y)) =>
    (s1, Int(y + 1))
}

ghost function Inc4(t: Triple): Pair
{
  match t
  case (s1, Int(x), Unknown) =>
    (s1, Int(x + 1))
  case (s1, Int(x), Int(y)) =>
    (s1, Int(x + y + 1))
  case (s1, Unknown, Unknown) =>
    (s1, Unknown)
  case (s1, Unknown, Int(y)) =>
    (s1, Int(y + 1))
}

method IncM(p: Pair)
{
}

method IncM2(s: string, t: EInt)
{
  match (s, t) {
    case {:split false} (s, Int(x)) =>
    case {:split false} (s, Unknown) =>
  }
}

method IncM3(s1: string, t1: EInt, t2: EInt)
{
  match (s1, t1, t2)
  case {:split false} (s1, Int(x), Unknown) =>
  case {:split false} (s1, Int(x), Int(y)) =>
  case {:split false} (s1, Unknown, Unknown) =>
  case {:split false} (s1, Unknown, Int(y)) =>
}

method IncM4(t: Triple)
{
  match t
  case {:split false} (s1, Int(x), Unknown) =>
  case {:split false} (s1, Int(x), Int(y)) =>
  case {:split false} (s1, Unknown, Unknown) =>
  case {:split false} (s1, Unknown, Int(y)) =>
}

datatype EInt = Int(val: int) | Unknown

type Pair = (string, EInt)

type Triple = (string, EInt, EInt)
