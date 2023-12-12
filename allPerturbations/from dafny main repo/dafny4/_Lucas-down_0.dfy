
// Lucas-down.dfy

ghost predicate Bit(k: nat, n: nat)
{
  if k == 0 then
    n % 2 == 1
  else
    Bit(k - 1, n / 2)
}

ghost function BitSet(n: nat): set<nat>
{
  set i | 0 <= i < n && Bit(i, n)
}

lemma BitSize(i: nat, n: nat)
  requires Bit(i, n)
  ensures i < n
{
}

ghost predicate EVEN(n: nat)
{
  n % 2 == 0
}

ghost function binom(a: nat, b: nat): nat
{
  if b == 0 then
    1
  else if a == 0 then
    0
  else
    binom(a - 1, b) + binom(a - 1, b - 1)
}

lemma Lucas_Binary''(a: nat, b: nat)
  ensures binom(a, b) % 2 == if EVEN(a) && !EVEN(b) then 0 else binom(a / 2, b / 2) % 2
{
  if a == 0 <==> b == 0 {
  } else {
    Lucas_Binary''(a - 1, b);
    Lucas_Binary''(a - 1, b - 1);
  }
}

ghost function Suc(S: set<nat>): set<nat>
{
  set x | x in S :: x + 1
}

lemma SucElements(S: set<nat>)
  ensures forall x :: x in S <==> x + 1 in Suc(S)
{
}

lemma BitSet_Property(n: nat)
  ensures BitSet(n) - {0} == Suc(BitSet(n / 2))
{
  if n == 0 {
  } else {
    forall x: nat | true {
      calc {
        x in BitSet(n) - {0};
      ==
        x != 0 &&
        x in BitSet(n);
      ==
        0 < x < n &&
        Bit(x, n);
      ==
        0 < x < n &&
        Bit(x - 1, n / 2);
      ==
        {
          if 0 < x && Bit(x - 1, n / 2) {
            BitSize(x - 1, n / 2);
          }
        }
        0 <= x - 1 < n / 2 &&
        Bit(x - 1, n / 2);
      ==
        x - 1 in BitSet(n / 2);
      ==
        {
          SucElements(BitSet(n / 2));
        }
        x in Suc(BitSet(n / 2));
      }
    }
  }
}

lemma Lucas_Theorem'(m: nat, n: nat)
  ensures BitSet(m) <= BitSet(n) <==> !EVEN(binom(n, m))
{
  if m == 0 && n == 0 {
  } else if EVEN(n) && !EVEN(m) {
    calc {
      !EVEN(binom(n, m));
    ==
      {
        Lucas_Binary''(n, m);
      }
      false;
    ==
      {
        assert 0 in BitSet(m) && 0 !in BitSet(n);
      }
      BitSet(m) <= BitSet(n);
    }
  } else {
    var m', n' := m / 2, n / 2;
    calc {
      !EVEN(binom(n, m));
    ==
      {
        Lucas_Binary''(n, m);
      }
      !EVEN(binom(n', m'));
    ==
      {
        Lucas_Theorem'(m', n');
      }
      BitSet(m') <= BitSet(n');
    ==
      {
        SucElements(BitSet(m'));
        SucElements(BitSet(n'));
      }
      Suc(BitSet(m')) <= Suc(BitSet(n'));
    ==
      {
        BitSet_Property(m);
        BitSet_Property(n);
      }
      BitSet(m) - {0} <= BitSet(n) - {0};
    ==
      {
        assert 0 !in BitSet(m) ==> BitSet(m) == BitSet(m) - {0};
        assert 0 in BitSet(n) ==> BitSet(n) - {0} <= BitSet(n);
      }
      BitSet(m) <= BitSet(n);
    }
  }
}
