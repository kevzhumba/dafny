
// git-issue75.dfy

ghost function f(): t

ghost function g(): int

lemma L1() returns (m: map<int, t>)
{
}

lemma L2() returns (m: map<int, t>)
{
  m := map i | 0 <= i < 5 :: [f()][0];
}

type t = i: int
  | 0 <= i < 10
