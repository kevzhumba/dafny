
// TreeFill.dfy

ghost function Contains<T>(t: Tree, v: T): bool
{
  match t
  case Leaf =>
    false
  case Node(left, x, right) =>
    x == v || Contains(left, v) || Contains(right, v)
}

method Fill<T>(t: Tree, a: array<T>, start: int)
    returns (end: int)
  requires 0 <= start <= a.Length
  modifies a
  ensures start <= end <= a.Length
  ensures forall i :: 0 <= i < start ==> a[i] == old(a[i])
  ensures forall i :: start <= i < end ==> Contains(t, a[i])
{
  match t
  case {:split false} Leaf =>
    end := start;
  case {:split false} Node(left, x, right) =>
    end := Fill(left, a, start);
    if end == a.Length {
      a[end] := x;
      end := Fill(right, a, end + 1);
    }
}

datatype Tree<T> = Leaf | Node(Tree, T, Tree)
