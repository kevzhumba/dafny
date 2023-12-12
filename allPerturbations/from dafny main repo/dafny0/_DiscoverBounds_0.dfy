
// DiscoverBounds.dfy

method Main()
{
}

predicate P(x: int)
{
  x == 157
}

predicate Q(r: real)
{
  r / 2.0 <= r
}

method OtherEq<U, V(==)>(b: bool, s: set<int>, t: seq<real>, u: map<U, V>, v: multiset<char>, w: iset<bv12>, x: imap<bv28, int>)
    returns (s': set<int>, t': seq<real>, u': map<U, V>, v': multiset<char>, w': iset<bv12>, x': imap<bv28, int>)
{
  if b {
    s' :| s' == s;
    t' :| t' == t;
    u' :| u' == u;
    v' :| v' == v;
    w' :| w' == w;
    x' :| x' == x;
  } else {
    s' := var s'' :| s'' == s; s'';
    t' := var t'' :| t'' == t; t'';
    u' := var u'' :| u'' == u; u'';
    v' := var v'' :| v'' == v; v'';
    w' := var w'' :| w'' == w; w'';
    x' := var x'' :| x'' == x; x'';
  }
}

newtype NT = x
  | 0 <= x < 100

newtype UT = NT

newtype Lower = x
  | -2 <= x

newtype Upper = x: Lower
  | x < 100

newtype Int = int

newtype NR = r
  | -2.0 <= r <= 5.4
