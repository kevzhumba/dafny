
// GenericSort.dfy

method Main()
{
  Client.TheMain();
  AnotherClient.TheMain();
}

abstract module TotalOrder {
  predicate Leq(a: T, b: T)

  lemma Antisymmetry(a: T, b: T)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b

  lemma Transitivity(a: T, b: T, c: T)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)

  lemma Totality(a: T, b: T)
    ensures Leq(a, b) || Leq(b, a)

  type T
}

abstract module Sort {
  ghost predicate Sorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    reads a
    ensures Sorted(a, low, high) ==> forall i, j :: low <= i < j < high ==> O.Leq(a[i], a[j])
  {
    forall i, j :: 
      low <= i < j < high ==>
        O.Leq(a[i], a[j])
  }

  ghost predicate NeighborSorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    reads a
  {
    forall i :: 
      low < i < high ==>
        O.Leq(a[i - 1], a[i])
  }

  lemma NeighborSorted_implies_Sorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    requires NeighborSorted(a, low, high)
    ensures Sorted(a, low, high)
    decreases high - low
  {
    if low != high {
      NeighborSorted_implies_Sorted(a, low + 1, high);
      forall j | low + 1 < j < high {
        O.Transitivity(a[low], a[low + 1], a[j]);
      }
    }
  }

  method InsertionSort(a: array<O.T>)
    modifies a
    ensures Sorted(a, 0, a.Length)
    ensures multiset(a[..]) == old(multiset(a[..]))
  {
  }

  import O : TotalOrder
}

module IntOrder refines TotalOrder {
  predicate Leq ...
    ensures Leq(a, b) ==> a.i <= b.i
  {
    a.i <= b.i
  }

  lemma Antisymmetry ...
  {
  }

  lemma Transitivity ...
  {
  }

  lemma Totality ...
  {
  }

  datatype T = Int(i: int)
}

module IntLexOrder refines TotalOrder {
  predicate Leq ...
  {
    if a.i < b.i then
      true
    else if a.i == b.i then
      a.j <= b.j
    else
      false
  }

  lemma Antisymmetry ...
  {
  }

  lemma Transitivity ...
  {
  }

  lemma Totality ...
  {
  }

  datatype T = Int(i: int, j: int)
}

module Client {
  method TheMain()
  {
    var a := new I.T[4];
    a[0] := I.T.Int(6);
    a[1] := I.T.Int(1);
    a[2] := I.T.Int(0);
    a[3] := I.T.Int(4);
    assert a[..] == [I.T.Int(6), I.T.Int(1), I.T.Int(0), I.T.Int(4)];
    IntSort.InsertionSort(a);
    assert IntSort.O.Leq(a[0], a[1]);
    assert IntSort.O.Leq(a[1], a[2]);
    assert IntSort.O.Leq(a[2], a[3]);
    assert a[..] == [I.T.Int(0), I.T.Int(1), I.T.Int(4), I.T.Int(6)];
    print a[..], "\n";
  }

  module IntSort refines Sort {

    import O = IntOrder
  }

  import I = IntOrder
}

module intOrder refines TotalOrder {
  predicate Leq ...
    ensures Leq(a, b) ==> a <= b
  {
    a <= b
  }

  lemma Antisymmetry ...
  {
  }

  lemma Transitivity ...
  {
  }

  lemma Totality ...
  {
  }

  type T = int
}

module AnotherClient {
  method TheMain()
  {
    var a := new int[4];
    a[0] := 6;
    a[1] := 1;
    a[2] := 0;
    a[3] := 4;
    assert a[..] == [6, 1, 0, 4];
    intSort.InsertionSort(a);
    assert intSort.O.Leq(a[0], a[1]);
    assert intSort.O.Leq(a[1], a[2]);
    assert intSort.O.Leq(a[2], a[3]);
    assert a[..] == [0, 1, 4, 6];
    print a[..], "\n";
  }

  module intSort refines Sort {

    import O = intOrder
  }

  import I = intOrder
}
