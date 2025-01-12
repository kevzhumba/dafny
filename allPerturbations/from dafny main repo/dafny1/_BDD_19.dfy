
// BDD.dfy


module SimpleBDD {
  class BDDNode {
    static ghost predicate bitfunc(f: map<seq<bool>, bool>, n: nat)
    {
      forall i: seq<bool> :: 
        i in f <==> |i| == n
    }

    ghost var Contents: map<seq<bool>, bool>
    ghost var Repr: set<object>
    ghost var n: nat
    var f: BDDNode?
    var t: BDDNode?
    var b: bool

    ghost predicate valid()
      reads this, Repr
    {
      bitfunc(Contents, n) &&
      (0 == n ==>
        (b <==> Contents[[]])) &&
      (0 < n ==>
        this in Repr &&
        f != null &&
        t != null &&
        t in Repr &&
        f in Repr &&
        t.Repr <= Repr &&
        f.Repr <= Repr &&
        this !in f.Repr &&
        this !in t.Repr &&
        t.valid() &&
        f.valid() &&
        t.n == f.n == n - 1 &&
        (forall s | s in t.Contents :: 
          Contents[[true] + s] <==> t.Contents[s]) &&
        forall s | s in f.Contents :: 
          Contents[[false] + s] <==> f.Contents[s])
    }
  }

  class BDD {
    var root: BDDNode

    ghost predicate valid()
      reads this, Repr
    {
      root in Repr &&
      root.Repr <= Repr &&
      root.valid() &&
      n == root.n &&
      Contents == root.Contents
    }

    constructor ()
    {
      root := new BDDNode;
    }

    ghost var Contents: map<seq<bool>, bool>
    var n: nat
    ghost var Repr: set<object>

    method Eval(s: seq<bool>) returns (b: bool)
      requires valid() && |s| == n
      ensures b == Contents[s]
    {
    }
  }
}
