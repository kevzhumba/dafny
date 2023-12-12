
// SeparationLogicList.dfy

class Node<T(0)> {
  var data: T
  var next: Node?<T>

  static ghost predicate ListSegment(q: seq<T>, from: Node?<T>, to: Node?<T>, S: set<Node<T>>)
    reads S
  {
    if q == [] then
      from == to
    else
      from != null && from in S && from.data == q[0] && ListSegment(q[1..], from.next, to, S - {from})
  }

  static method Create(x: T) returns (l: Node<T>, ghost S: set<Node<T>>)
    ensures ListSegment([x], l, null, S) && fresh(S)
  {
    if * {
    } else {
      l, S := Cons(x, null, [], {});
    }
  }

  static method Cons(x: T, tail: Node?<T>, ghost q: seq<T>, ghost S: set<Node<T>>)
      returns (l: Node<T>, ghost U: set<Node<T>>)
    requires ListSegment(q, tail, null, S)
    ensures ListSegment([x] + q, l, null, U) && fresh(U - S)
  {
    l := new Node<T>;
    l.data := x;
    l.next := tail;
    U := S + {l};
  }
}

class ListNode<T(0)> {
  ghost var Contents: seq<T>
  ghost var Repr: set<ListNode<T>>
  var data: T
  var next: ListNode?<T>

  static ghost predicate IsList(l: ListNode?<T>)
    reads l, if l != null then l.Repr else {}
  {
    if l == null then
      true
    else if l.next == null then
      l in l.Repr &&
      l.Contents == [l.data]
    else
      {l, l.next} <= l.Repr && l.Contents == [l.data] + l.next.Contents && l.next.Repr <= l.Repr - {l} && IsList(l.next)
  }

  static method Create(x: T) returns (l: ListNode<T>)
    ensures IsList(l) && l.Contents == [x] && fresh({l} + l.Repr)
  {
    if * {
      l := new ListNode<T>;
      l.data := x;
      l.next := null;
      l.Repr := {l};
      l.Contents := [x];
    } else {
      l := Cons(x, null);
    }
  }

  static method Cons(x: T, tail: ListNode?<T>) returns (l: ListNode<T>)
    requires IsList(tail)
    ensures IsList(l)
    ensures tail == null ==> l.Contents == [x] && fresh({l} + l.Repr)
    ensures tail != null ==> l.Contents == [x] + tail.Contents && fresh({l} + l.Repr - tail.Repr)
  {
    l := new ListNode<T>;
    l.data := x;
    l.next := tail;
    if tail != null {
      l.Repr := tail.Repr + {l};
      l.Contents := [x] + tail.Contents;
    } else {
      l.Repr := {l};
      l.Contents := [x];
    }
  }
}

class List<T(0)> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object>
  var head: LLNode<T>

  ghost predicate IsList()
    reads this, Repr
  {
    this in Repr &&
    head in Repr &&
    head.Repr <= Repr &&
    this !in head.Repr &&
    head.IsWellFormed() &&
    Contents == head.TailContents
  }

  constructor Init()
    ensures IsList() && Contents == [] && fresh(Repr)
  {
    var h: LLNode<T> := new LLNode<T>;
    h.next := null;
    h.TailContents := [];
    h.Repr := {h};
    head := h;
    Contents := [];
    Repr := {this} + h.Repr;
  }

  method Cons(x: T)
    requires IsList()
    modifies Repr
    ensures IsList() && Contents == [x] + old(Contents) && fresh(Repr - old(Repr))
  {
    head.data := x;
    assert head.IsWellFormed();
    var h: LLNode<T> := new LLNode<T>;
    h.next := head;
    h.TailContents := [x] + head.TailContents;
    h.Repr := {h} + head.Repr;
    head := h;
    Contents := [x] + Contents;
    Repr := Repr + {h};
  }
}

class LLNode<T(0)> {
  var data: T
  var next: LLNode?<T>
  ghost var TailContents: seq<T>
  ghost var Repr: set<object>

  ghost predicate IsWellFormed()
    reads this, Repr
  {
    this in Repr &&
    (next == null ==>
      TailContents == []) &&
    (next != null ==>
      next in Repr &&
      next.Repr <= Repr &&
      this !in next.Repr &&
      next.IsWellFormed() &&
      TailContents == [next.data] + next.TailContents)
  }
}
