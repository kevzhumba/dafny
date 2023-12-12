
// COST-verif-comp-2011-4-FloydCycleDetect.dfy

class Node {
  var next: Node?

  ghost predicate IsClosed(S: set<Node?>)
    reads S
  {
    this in S &&
    null in S &&
    forall n :: 
      n in S &&
      n != null &&
      n.next != null ==>
        n.next in S
  }

  ghost function Nexxxt(k: int, S: set<Node?>): Node?
    requires IsClosed(S) && 0 <= k
    reads S
    ensures Nexxxt(k, S) in S
  {
    if k == 0 then
      this
    else if Nexxxt(k - 1, S) == null then
      null
    else
      Nexxxt(k - 1, S).next
  }

  ghost predicate Reaches(sink: Node, S: set<Node?>)
    requires IsClosed(S)
    reads S
    ensures Reaches(sink, S) ==> sink in S
  {
    exists k :: 
      0 <= k &&
      Nexxxt(k, S) == sink
  }

  method Cyclic(ghost S: set<Node?>) returns (reachesCycle: bool)
    requires IsClosed(S)
    ensures reachesCycle <==> exists n :: Reaches(n, S) && n.next != null && n.next.Reaches(n, S)
  {
    ghost var A, B := AnalyzeList(S);
    var tortoise, hare := this, next;
    ghost var t, h := 0, 1;
    while hare != tortoise
      invariant tortoise != null && tortoise in S && hare in S
      invariant 0 <= t < h && Nexxxt(t, S) == tortoise && Nexxxt(h, S) == hare
      invariant h == 1 + 2 * t && t <= A + B
      invariant forall k :: 0 <= k < t ==> Nexxxt(k, S) != Nexxxt(1 + 2 * k, S)
      decreases A + B - t
    {
      if hare == null || hare.next == null {
        ghost var distanceToNull := if hare == null then h else h + 1;
        Lemma_NullImpliesNoCycles(distanceToNull, S);
        assert !exists k, l :: 0 <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null && Nexxxt(k, S).next.Nexxxt(l, S) == Nexxxt(k, S);
        return false;
      }
      Lemma_NullIsTerminal(h + 1, S);
      assert Nexxxt(t + 1, S) != null;
      tortoise, t, hare, h := tortoise.next, t + 1, hare.next.next, h + 2;
      CrucialLemma(A, B, S);
    }
    Lemma_NullIsTerminal(h, S);
    Lemma_NexxxtIsTransitive(t + 1, h - (t + 1), S);
    assert tortoise.next.Reaches(tortoise, S);
    return true;
  }

  lemma AnalyzeList(S: set<Node?>) returns (A: int, B: int)
    requires IsClosed(S)
    ensures 0 <= A && 1 <= B
    ensures Nexxxt(A, S) != null ==> Nexxxt(A, S) == Nexxxt(A, S).Nexxxt(B, S)
    ensures forall k, l :: 0 <= k < l < A ==> Nexxxt(k, S) != Nexxxt(l, S)
  {
    var p, steps, Visited, NexxxtInverse: map<Node?, int> := this, 0, {null}, map[];
    while p !in Visited
      invariant 0 <= steps && p == Nexxxt(steps, S) && p in S && null in Visited && Visited <= S
      invariant forall t :: 0 <= t < steps ==> Nexxxt(t, S) in Visited && Nexxxt(t, S) in NexxxtInverse && NexxxtInverse[Nexxxt(t, S)] == t
      invariant forall q :: q in Visited && q != null ==> q in NexxxtInverse && 0 <= NexxxtInverse[q] < steps && Nexxxt(NexxxtInverse[q], S) == q
      decreases S - Visited
    {
      p, steps, Visited, NexxxtInverse := p.next, steps + 1, Visited + {p}, NexxxtInverse[p := steps];
    }
    if p == null {
      A, B := steps, 1;
    } else {
      A := NexxxtInverse[p];
      B := steps - A;
      Lemma_NexxxtIsTransitive(A, B, S);
    }
  }

  lemma CrucialLemma(a: int, b: int, S: set<Node?>)
    requires IsClosed(S)
    requires 0 <= a && 1 <= b
    requires forall k, l :: 0 <= k < l < a ==> Nexxxt(k, S) != Nexxxt(l, S)
    requires Nexxxt(a, S) == null || Nexxxt(a, S).Nexxxt(b, S) == Nexxxt(a, S)
    ensures exists T :: 0 <= T < a + b && Nexxxt(T, S) == Nexxxt(1 + 2 * T, S)
  {
    if Nexxxt(a, S) == null {
      Lemma_NullIsTerminal(1 + 2 * a, S);
      assert Nexxxt(a, S) == null ==> Nexxxt(1 + 2 * a, S) == null;
    } else {
    }
  }

  lemma {:induction false} Lemma_AboutCycles(a: int, b: int, k: int, S: set<Node?>)
    requires IsClosed(S)
    requires 0 <= a <= k && 1 <= b && Nexxxt(a, S) != null && Nexxxt(a, S).Nexxxt(b, S) == Nexxxt(a, S)
    ensures Nexxxt(k + b, S) == Nexxxt(k, S)
  {
    Lemma_NexxxtIsTransitive(a, b, S);
    var n := a;
    while n < k
      invariant a <= n <= k
      invariant Nexxxt(n + b, S) == Nexxxt(n, S)
    {
      n := n + 1;
    }
  }

  lemma Lemma_NexxxtIsTransitive(x: int, y: int, S: set<Node?>)
    requires IsClosed(S) && 0 <= x && 0 <= y
    ensures Nexxxt(x, S) != null ==> Nexxxt(x, S).Nexxxt(y, S) == Nexxxt(x + y, S)
  {
    if Nexxxt(x, S) != null {
      assert forall j {:induction} :: 0 <= j ==> Nexxxt(x, S).Nexxxt(j, S) == Nexxxt(x + j, S);
    }
  }

  lemma Lemma_NullIsTerminal(d: int, S: set<Node?>)
    requires IsClosed(S) && 0 <= d
    ensures forall k :: 0 <= k < d && Nexxxt(d, S) != null ==> Nexxxt(k, S) != null
  {
    var j := d;
    while 0 < j
      invariant 0 <= j <= d
      invariant forall k :: j <= k < d && Nexxxt(k, S) == null ==> Nexxxt(d, S) == null
    {
      j := j - 1;
      if Nexxxt(j, S) == null {
        assert Nexxxt(j + 1, S) == null;
      }
    }
  }

  lemma Lemma_NullImpliesNoCycles(n: int, S: set<Node?>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures !exists k, l :: 0 <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null && Nexxxt(k, S).next.Nexxxt(l, S) == Nexxxt(k, S)
  {
    Lemma_NullImpliesNoCycles_part0(n, S);
    Lemma_NullImpliesNoCycles_part1(n, S);
    Lemma_NullImpliesNoCycles_part2(n, S);
  }

  lemma Lemma_NullImpliesNoCycles_part0(n: int, S: set<Node?>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures forall k, l :: n <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
  {
    assert forall k {:induction} :: n <= k ==> Nexxxt(k, S) == null;
  }

  lemma Lemma_NullImpliesNoCycles_part1(n: int, S: set<Node?>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures forall k, l :: 0 <= k && n <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
  {
    assert forall k, l {:matchinglooprewrite false} {:induction} :: 0 <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) == Nexxxt(k + 1 + l, S);
    assert forall kl {:induction} :: n <= kl ==> Nexxxt(kl, S) == null;
  }

  lemma Lemma_NullImpliesNoCycles_part2(n: int, S: set<Node?>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures forall k, l :: 0 <= k < n && 0 <= l < n && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
  {
    var kn := 0;
    while kn < n
      invariant 0 <= kn <= n
      invariant forall k, l :: 0 <= k < kn && 0 <= l < n && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
    {
      var ln := 0;
      while ln < n
        invariant 0 <= ln <= n
        invariant forall k, l :: 0 <= k < kn && 0 <= l < n && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
        invariant forall l :: 0 <= l < ln && Nexxxt(kn, S) != null && Nexxxt(kn, S).next != null ==> Nexxxt(kn, S).next.Nexxxt(l, S) != Nexxxt(kn, S)
      {
        if Nexxxt(kn, S) != null && Nexxxt(kn, S).next != null {
          assert Nexxxt(kn + 1, S) != null;
          Lemma_NexxxtIsTransitive(kn + 1, ln, S);
          assert Nexxxt(kn, S).next.Nexxxt(ln, S) == Nexxxt(kn + 1 + ln, S);
          Lemma_NexxxtIsTransitive(kn, 1 + ln, S);
          assert Nexxxt(kn + 1 + ln, S) == Nexxxt(kn, S).Nexxxt(1 + ln, S);
          if Nexxxt(kn, S).Nexxxt(1 + ln, S) == Nexxxt(kn, S) {
            var nn := 1 + ln;
            while nn < n
              invariant 0 <= nn
              invariant Nexxxt(kn, S).Nexxxt(nn, S) == Nexxxt(kn, S)
            {
              assert Nexxxt(kn, S) == Nexxxt(kn, S).Nexxxt(nn, S) == Nexxxt(kn, S).Nexxxt(1 + ln, S) == Nexxxt(kn, S).Nexxxt(nn, S).Nexxxt(1 + ln, S);
              Nexxxt(kn, S).Lemma_NexxxtIsTransitive(1 + ln, nn, S);
              assert Nexxxt(kn, S).Nexxxt(nn + 1 + ln, S) == Nexxxt(kn, S);
              nn := nn + 1 + ln;
            }
            Lemma_NexxxtIsTransitive(kn, nn, S);
            assert Nexxxt(kn, S).Nexxxt(nn, S) == Nexxxt(kn + nn, S);
            assert forall j {:induction} :: n <= j ==> Nexxxt(j, S) == null;
            assert false;
          }
          assert Nexxxt(kn + 1, S).Nexxxt(ln, S) != Nexxxt(kn, S);
        }
        ln := ln + 1;
      }
      kn := kn + 1;
    }
  }
}
