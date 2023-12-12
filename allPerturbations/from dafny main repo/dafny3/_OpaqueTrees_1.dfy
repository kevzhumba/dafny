
// OpaqueTrees.dfy

ghost function {:opaque} size(t: Tree): nat
{
  match t
  case Leaf(_ /* _v3 */) =>
    1
  case Node(left, right) =>
    1 + size(left) + size(right)
}

ghost function {:opaque} mirror<T>(t: Tree<T>): Tree<T>
{
  match t
  case Leaf(_ /* _v4 */) =>
    t
  case Node(left, right) =>
    Node(mirror(right), mirror(left))
}

lemma {:induction false} MirrorSize(t: Tree)
  ensures size(mirror(t)) == size(t)
{
  match t {
    case {:split false} Leaf(x) =>
      calc {
        size(mirror(Leaf(x)));
      ==
        {
          reveal mirror();
        }
        size(Leaf(x));
      }
    case {:split false} Node(left, right) =>
  }
}

datatype Tree<T> = Leaf(T) | Node(Tree, Tree)
