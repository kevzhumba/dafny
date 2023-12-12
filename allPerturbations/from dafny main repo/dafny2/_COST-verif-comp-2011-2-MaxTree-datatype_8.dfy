
// COST-verif-comp-2011-2-MaxTree-datatype.dfy

ghost function Contains(t: Tree, v: int): bool
{
  match t
  case Null =>
    false
  case Node(left, x, right) =>
    x == v || Contains(left, v) || Contains(right, v)
}

method Max(t: Tree) returns (result: int)
  requires t != Null
  ensures Contains(t, result) && forall v :: Contains(t, v) ==> v <= result
{
  match t {
    case {:split false} Node(left, x, right) =>
      result := MaxAux(right, x);
      result := MaxAux(left, result);
  }
}

method MaxAux(t: Tree, acc: int) returns (result: int)
  ensures result == acc || Contains(t, result)
  ensures acc <= result && forall v :: Contains(t, v) ==> v <= result
{
  match t {
    case {:split false} Null =>
      result := acc;
    case {:split false} Node(left, x, right) =>
      result := MaxAux(right, if x < acc then acc else x);
  }
}

datatype Tree = Null | Node(Tree, int, Tree)
