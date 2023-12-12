
// ReverseLinkedList.dfy

function reverse<A>(x: seq<A>): seq<A>
{
  if x == [] then
    []
  else
    reverse(x[1..]) + [x[0]]
}

function nodeConcat(xs: ListNode, end: ListNode): ListNode
{
  if xs == Null then
    end
  else
    Node(xs.val, nodeConcat(xs.next, end))
}

function reverseList(xs: ListNode): ListNode
{
  if xs == Null then
    Null
  else
    nodeConcat(reverseList(xs.next), Node(xs.val, Null))
}

lemma ConcatNullIsRightIdentity(xs: ListNode)
  ensures xs == nodeConcat(xs, Null)
{
}

lemma ConcatNullIsLeftIdentity(xs: ListNode)
  ensures xs == nodeConcat(Null, xs)
{
}

lemma ConcatExtensionality(xs: ListNode)
  requires xs != Null
  ensures nodeConcat(Node(xs.val, Null), xs.next) == xs
{
}

lemma ConcatAssociative(xs: ListNode, ys: ListNode, zs: ListNode)
  ensures nodeConcat(nodeConcat(xs, ys), zs) == nodeConcat(xs, nodeConcat(ys, zs))
{
}

lemma reverseSingleList(xs: ListNode)
  requires xs != Null
  requires xs.next == Null
  ensures reverseList(xs) == xs
{
}

lemma {:verify true} ConcatReverseList(xs: ListNode, ys: ListNode)
  ensures reverseList(nodeConcat(xs, ys)) == nodeConcat(reverseList(ys), reverseList(xs))
  decreases xs
{
  if xs == Null {
    calc {
      reverseList(nodeConcat(xs, ys));
    ==
      {
        ConcatNullIsLeftIdentity(ys);
      }
      reverseList(ys);
    ==
      {
        ConcatNullIsRightIdentity(reverseList(ys));
      }
      nodeConcat(reverseList(ys), Null);
      nodeConcat(reverseList(ys), xs);
      nodeConcat(reverseList(ys), reverseList(xs));
    }
  } else {
    var x := Node(xs.val, Null);
    calc {
      reverseList(nodeConcat(xs, ys));
      reverseList(nodeConcat(nodeConcat(x, xs.next), ys));
    ==
      {
        ConcatAssociative(x, xs.next, ys);
      }
      reverseList(nodeConcat(x, nodeConcat(xs.next, ys)));
      nodeConcat(reverseList(nodeConcat(xs.next, ys)), x);
    ==
      {
        ConcatReverseList(xs.next, ys);
      }
      nodeConcat(nodeConcat(reverseList(ys), reverseList(xs.next)), x);
    ==
      {
        ConcatAssociative(reverseList(ys), reverseList(xs.next), x);
      }
      nodeConcat(reverseList(ys), nodeConcat(reverseList(xs.next), x));
      nodeConcat(reverseList(ys), reverseList(xs));
    }
  }
}

lemma reverseReverseListIsIdempotent(xs: ListNode)
  ensures reverseList(reverseList(xs)) == xs
{
  if xs == Null {
  } else {
    var x := Node(xs.val, Null);
    calc {
      reverseList(reverseList(xs));
      reverseList(reverseList(nodeConcat(x, xs.next)));
    ==
      {
        ConcatReverseList(x, xs.next);
      }
      reverseList(nodeConcat(reverseList(xs.next), reverseList(x)));
      reverseList(nodeConcat(reverseList(xs.next), x));
    ==
      {
        ConcatReverseList(reverseList(xs.next), x);
      }
      nodeConcat(reverseList(x), reverseList(reverseList(xs.next)));
      nodeConcat(x, reverseList(reverseList(xs.next)));
      nodeConcat(x, xs.next);
      xs;
    }
  }
}

lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>)
  ensures multiset(xs) == multiset(reverse(xs))
{
  if xs == [] {
  } else {
    var x := xs[0];
    assert xs == [x] + xs[1..];
    assert multiset(xs) == multiset([x]) + multiset(xs[1..]);
    assert reverse(xs) == reverse(xs[1..]) + [x];
    reversePreservesMultiset(xs[1..]);
    assert multiset(xs[1..]) == multiset(reverse(xs[1..]));
  }
}

lemma reversePreservesLength<A>(xs: seq<A>)
  ensures |xs| == |reverse(xs)|
{
}

lemma lastReverseIsFirst<A>(xs: seq<A>)
  requires |xs| > 0
  ensures xs[0] == reverse(xs)[|reverse(xs)| - 1]
{
  reversePreservesLength(xs);
  assert |xs| == |reverse(xs)|;
}

lemma firstReverseIsLast<A>(xs: seq<A>)
  requires |xs| > 0
  ensures reverse(xs)[0] == xs[|xs| - 1]
{
}

lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
  ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
}

lemma reverseRest<A>(xs: seq<A>)
  requires |xs| > 0
  ensures reverse(xs) == [xs[|xs| - 1]] + reverse(xs[0 .. |xs| - 1])
{
  firstReverseIsLast(xs);
  assert xs == xs[0 .. |xs| - 1] + [xs[|xs| - 1]];
  assert reverse(xs)[0] == xs[|xs| - 1];
  assert reverse(xs) == [xs[|xs| - 1]] + reverse(xs)[1..];
  calc {
    reverse(xs);
    reverse(xs[0 .. |xs| - 1] + [xs[|xs| - 1]]);
  ==
    {
      ReverseConcat(xs[0 .. |xs| - 1], [xs[|xs| - 1]]);
    }
    reverse([xs[|xs| - 1]]) + reverse(xs[0 .. |xs| - 1]);
  }
}

lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
  requires |xs| == |ys|
  requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
  ensures xs == ys
{
}

lemma ReverseIndexAll<T>(xs: seq<T>)
  ensures |reverse(xs)| == |xs|
  ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
{
}

lemma ReverseIndex<T>(xs: seq<T>, i: int)
  requires 0 <= i < |xs|
  ensures |reverse(xs)| == |xs|
  ensures reverse(xs)[i] == xs[|xs| - i - 1]
{
  ReverseIndexAll(xs);
  assert forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1];
}

lemma ReverseSingle<A>(xs: seq<A>)
  requires |xs| == 1
  ensures reverse(xs) == xs
{
}

lemma reverseReverseIdempotent<A>(xs: seq<A>)
  ensures reverse(reverse(xs)) == xs
{
  if xs == [] {
  } else {
    calc {
      reverse(reverse(xs));
      reverse(reverse([xs[0]] + xs[1..]));
    ==
      {
        ReverseConcat([xs[0]], xs[1..]);
      }
      reverse(reverse(xs[1..]) + reverse([xs[0]]));
    ==
      {
        ReverseSingle([xs[0]]);
      }
      reverse(reverse(xs[1..]) + [xs[0]]);
    ==
      {
        ReverseConcat(reverse(xs[1..]), [xs[0]]);
      }
      reverse([xs[0]]) + reverse(reverse(xs[1..]));
      [xs[0]] + reverse(reverse(xs[1..]));
    ==
      {
        reverseReverseIdempotent(xs[1..]);
      }
      xs;
    }
  }
}

method test()
{
  var cycle := Node(1, Null);
  var next := Node(2, cycle);
}

datatype ListNode = Null | Node(val: nat, next: ListNode)
