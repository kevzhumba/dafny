
// ListReverse.dfy

class Node {
  var nxt: Node?

  method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    requires x == null || x in r
    requires forall y :: y in r ==> y.nxt == null || y.nxt in r
    modifies r
    ensures reverse == null || reverse in r
    ensures forall y :: y in r ==> y.nxt == null || y.nxt in r
    decreases *
  {
  }
}
