
// COST-verif-comp-2011-2-MaxTree-class.dfy

class Tree {
  var value: int
  var left: Tree?
  var right: Tree?
  ghost var Contents: seq<int>
  ghost var Repr: set<object>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    left != null &&
    right != null &&
    ((left == this == right && Contents == []) || (left in Repr && left.Repr <= Repr && this !in left.Repr && right in Repr && right.Repr <= Repr && this !in right.Repr && left.Valid() && right.Valid() && Contents == left.Contents + [value] + right.Contents))
  }

  function IsEmpty(): bool
    requires Valid()
    reads this, Repr
    ensures IsEmpty() <==> Contents == []
  {
    left == this
  }

  constructor Empty()
    ensures Valid() && Contents == []
  {
    left, right := this, this;
    Contents := [];
    Repr := {this};
  }

  constructor Node(lft: Tree, val: int, rgt: Tree)
    requires lft.Valid() && rgt.Valid()
    ensures Valid() && Contents == lft.Contents + [val] + rgt.Contents
  {
  }

  lemma exists_intro<T>(P: T ~> bool, x: T)
    requires P.requires(x)
    requires P(x)
    ensures exists y :: P.requires(y) && P(y)
  {
  }

  method ComputeMax() returns (mx: int)
    requires Valid() && !IsEmpty()
    ensures forall x :: x in Contents ==> x <= mx
    ensures exists x :: x in Contents && x == mx
    decreases Repr
  {
    mx := value;
    if !left.IsEmpty() {
      var m := left.ComputeMax();
      mx := if mx < m then m else mx;
    }
    if !right.IsEmpty() {
      var m := right.ComputeMax();
      mx := if mx < m then m else mx;
    }
    exists_intro(x reads this => x in Contents && x == mx, mx);
  }
}
