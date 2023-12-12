
// git-issue67.dfy

ghost predicate Q(x: Node)

ghost predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
{
  forall x | Q(x)
    ensures P(x)
  {
    assume false;
  }
  assert forall x :: Q(x) ==> P(x);
}

class Node { }
