
// InfiniteTrees.dfy

ghost function Tail(s: Stream, n: nat): Stream
{
  if n == 0 then
    s
  else
    var t := Tail(s, n - 1); if t == Nil then t else t.tail
}

lemma Tail_Lemma0(s: Stream, n: nat)
  requires s.Cons? && Tail(s, n).Cons?
  ensures Tail(s, n).tail == Tail(s.tail, n)
{
}

lemma Tail_Lemma1(s: Stream, k: nat, n: nat)
  requires k <= n
  ensures Tail(s, n).Cons? ==> Tail(s, k).Cons?
{
  if (k < n) == Tail(s, n).Cons? {
    assert Tail(s, n) == Tail(s, n - 1).tail;
  }
}

lemma Tail_Lemma2(s: Stream, n: nat)
  requires s.Cons? && Tail(s.tail, n).Cons?
  ensures Tail(s, n).Cons?
{
  if n != 0 {
    Tail_Lemma0(s, n - 1);
  }
}

greatest predicate IsNeverEndingStream<S>(s: Stream<S>)
{
  match s
  case Nil =>
    false
  case Cons(_ /* _v0 */, tail) =>
    IsNeverEndingStream(tail)
}

ghost function AnInfiniteStream(): Stream<int>
{
  Cons(0, AnInfiniteStream())
}

greatest lemma Proposition0()
  ensures IsNeverEndingStream(AnInfiniteStream())
{
}

ghost predicate HasBoundedHeight(t: Tree)
{
  exists n :: 
    0 <= n &&
    LowerThan(t.children, n)
}

greatest predicate LowerThan(s: Stream<Tree>, n: nat)
{
  match s
  case Nil =>
    true
  case Cons(t, tail) =>
    1 <= n &&
    LowerThan(t.children, n - 1) &&
    LowerThan(tail, n)
}

lemma LowerThan_Lemma(s: Stream<Tree>, n: nat, h: nat)
  ensures LowerThan(s, h) ==> LowerThan(Tail(s, n), h)
{
  Tail_Lemma1(s, 0, n);
  if n == 0 || Tail(s, n) == Nil {
  } else {
    match s {
      case {:split false} Cons(t, tail) =>
        LowerThan_Lemma(tail, n - 1, h);
        Tail_Lemma0(s, n - 1);
    }
  }
}

ghost predicate IsFiniteSomewhere(t: Tree)
{
  !InfiniteEverywhere(t.children)
}

greatest predicate InfiniteEverywhere(s: Stream<Tree>)
{
  match s
  case Nil =>
    false
  case Cons(t, tail) =>
    InfiniteEverywhere(t.children) &&
    InfiniteEverywhere(tail)
}

ghost function SkinnyTree(): Tree
{
  Node(Cons(SkinnyTree(), Nil))
}

lemma Proposition1()
  ensures IsFiniteSomewhere(SkinnyTree()) && !HasBoundedHeight(SkinnyTree())
{
  assert forall n {:induction} :: 0 <= n ==> !LowerThan(SkinnyTree().children, n);
}

lemma Theorem0(t: Tree)
  requires HasBoundedHeight(t)
  ensures IsFiniteSomewhere(t)
{
  var n :| 0 <= n && LowerThan(t.children, n);
  var k := FindNil(t.children, n);
}

lemma FindNil(s: Stream<Tree>, n: nat) returns (k: nat)
  requires LowerThan(s, n)
  ensures !InfiniteEverywhere#[k as ORDINAL](s)
{
  match s {
    case {:split false} Nil =>
      k := 1;
    case {:split false} Cons(t, _ /* _v1 */) =>
      k := FindNil(t.children, n - 1);
      k := k + 1;
  }
}

ghost predicate HasFiniteHeightEverywhere_Bad(t: Tree)
{
  !InfiniteHeightSomewhere_Bad(t.children)
}

greatest predicate InfiniteHeightSomewhere_Bad(s: Stream<Tree>)
{
  match s
  case Nil =>
    false
  case Cons(t, tail) =>
    InfiniteHeightSomewhere_Bad(t.children) || InfiniteHeightSomewhere_Bad(tail)
}

ghost function ATree(): Tree
{
  Node(ATreeChildren())
}

ghost function ATreeChildren(): Stream<Tree>
{
  Cons(Node(Nil), ATreeChildren())
}

lemma Proposition2()
  ensures !HasFiniteHeightEverywhere_Bad(ATree())
{
  Proposition2_Lemma0();
  Proposition2_Lemma1(ATreeChildren());
}

greatest lemma Proposition2_Lemma0()
  ensures IsNeverEndingStream(ATreeChildren())
{
}

greatest lemma Proposition2_Lemma1(s: Stream<Tree>)
  requires IsNeverEndingStream(s)
  ensures InfiniteHeightSomewhere_Bad(s)
{
  calc {
    InfiniteHeightSomewhere_Bad#[_k](s);
    InfiniteHeightSomewhere_Bad#[_k - 1](s.head.children) || InfiniteHeightSomewhere_Bad#[_k - 1](s.tail);
  <==
    InfiniteHeightSomewhere_Bad#[_k - 1](s.tail);
  }
}

greatest predicate ValidPath(t: Tree, p: Stream<int>)
{
  match p
  case Nil =>
    t == Node(Nil)
  case Cons(index, tail) =>
    0 <= index &&
    var ch := Tail(t.children, index); ch.Cons? && ValidPath(ch.head, tail)
}

lemma ValidPath_Lemma(p: Stream<int>)
  ensures ValidPath(Node(Nil), p) ==> p == Nil
{
  if ValidPath(Node(Nil), p) {
    match p {
      case {:split false} Nil =>
      case {:split false} Cons(index, tail) =>
        var nil: Stream<Tree> := Nil;
        Tail_Lemma1(nil, 0, index);
    }
  }
}

ghost predicate HasFiniteHeight(t: Tree)
{
  forall p :: 
    ValidPath(t, p) ==>
      !IsNeverEndingStream(p)
}

lemma Theorem1(t: Tree)
  requires HasBoundedHeight(t)
  ensures HasFiniteHeight(t)
{
  var n :| 0 <= n && LowerThan(t.children, n);
  forall p | ValidPath(t, p) {
    Theorem1_Lemma(t, n, p);
  }
}

lemma Theorem1_Lemma(t: Tree, n: nat, p: Stream<int>)
  requires LowerThan(t.children, n) && ValidPath(t, p)
  ensures !IsNeverEndingStream(p)
  decreases n
{
  match p {
    case {:split false} Nil =>
    case {:split false} Cons(index, tail) =>
      var ch := Tail(t.children, index);
      calc {
        LowerThan(t.children, n);
      ==>
        {
          LowerThan_Lemma(t.children, index, n);
        }
        LowerThan(ch, n);
      ==>
        LowerThan(ch.head.children, n - 1);
      ==>
        !IsNeverEndingStream(tail);
      ==>
        !IsNeverEndingStream(p);
      }
  }
}

ghost function SkinnyFiniteTree(n: nat): Tree
  ensures forall k: nat :: LowerThan(SkinnyFiniteTree(n).children, k) <==> n <= k
{
  if n == 0 then
    Node(Nil)
  else
    Node(Cons(SkinnyFiniteTree(n - 1), Nil))
}

ghost function FiniteUnboundedTree(): Tree
{
  Node(EverLongerSkinnyTrees(0))
}

ghost function EverLongerSkinnyTrees(n: nat): Stream<Tree>
{
  Cons(SkinnyFiniteTree(n), EverLongerSkinnyTrees(n + 1))
}

lemma EverLongerSkinnyTrees_Lemma(k: nat, n: nat)
  ensures Tail(EverLongerSkinnyTrees(k), n).Cons?
  ensures Tail(EverLongerSkinnyTrees(k), n).head == SkinnyFiniteTree(k + n)
  decreases n
{
  if n == 0 {
  } else {
    calc {
      Tail(EverLongerSkinnyTrees(k), n);
      {
        EverLongerSkinnyTrees_Lemma(k, n - 1);
      }
      Tail(EverLongerSkinnyTrees(k), n - 1).tail;
      {
        Tail_Lemma0(EverLongerSkinnyTrees(k), n - 1);
      }
      Tail(EverLongerSkinnyTrees(k).tail, n - 1);
      Tail(EverLongerSkinnyTrees(k + 1), n - 1);
    }
    EverLongerSkinnyTrees_Lemma(k + 1, n - 1);
  }
}

lemma Proposition3()
  ensures !HasBoundedHeight(FiniteUnboundedTree()) && HasFiniteHeight(FiniteUnboundedTree())
{
  Proposition3a();
  Proposition3b();
}

lemma Proposition3a()
  ensures !HasBoundedHeight(FiniteUnboundedTree())
{
  var ch := FiniteUnboundedTree().children;
  forall n | 0 <= n
    ensures !LowerThan(ch, n)
  {
    var cn := Tail(ch, n + 1);
    EverLongerSkinnyTrees_Lemma(0, n + 1);
    assert cn.head == SkinnyFiniteTree(n + 1);
    assert !LowerThan(cn.head.children, n);
    LowerThan_Lemma(ch, n + 1, n);
  }
}

lemma Proposition3b()
  ensures HasFiniteHeight(FiniteUnboundedTree())
{
  var t := FiniteUnboundedTree();
  forall p | ValidPath(t, p)
    ensures !IsNeverEndingStream(p)
  {
    assert p.Cons?;
    var index := p.head;
    assert 0 <= index;
    var ch := Tail(t.children, index);
    assert ch.Cons? && ValidPath(ch.head, p.tail);
    EverLongerSkinnyTrees_Lemma(0, index);
    assert ch.head == SkinnyFiniteTree(index);
    var si := SkinnyFiniteTree(index);
    assert LowerThan(si.children, index);
    Proposition3b_Lemma(si, index, p.tail);
  }
}

lemma Proposition3b_Lemma(t: Tree, h: nat, p: Stream<int>)
  requires LowerThan(t.children, h) && ValidPath(t, p)
  ensures !IsNeverEndingStream(p)
  decreases h
{
  match p {
    case {:split false} Nil =>
    case {:split false} Cons(index, tail) =>
      var ch := Tail(t.children, index);
      match t.children {
        case {:split false} Nil =>
          ValidPath_Lemma(p);
          assert false;
        case {:split false} Cons(_ /* _v2 */, _ /* _v3 */) =>
          LowerThan_Lemma(t.children, index, h);
      }
      assert LowerThan(ch.head.children, h - 1);
  }
}

greatest predicate InfinitePath(r: CoOption<Number>)
{
  match r
  case None =>
    false
  case Some(num) =>
    InfinitePath'(num)
}

greatest predicate InfinitePath'(num: Number)
{
  match num
  case Succ(next) =>
    InfinitePath'(next)
  case Zero(r) =>
    InfinitePath(r)
}

greatest predicate ValidPath_Alt(t: Tree, r: CoOption<Number>)
{
  match r
  case None =>
    t == Node(Nil)
  case Some(num) =>
    ValidPath_Alt'(t.children, num)
}

greatest predicate ValidPath_Alt'(s: Stream<Tree>, num: Number)
{
  match num
  case Succ(next) =>
    s.Cons? &&
    ValidPath_Alt'(s.tail, next)
  case Zero(r) =>
    s.Cons? &&
    ValidPath_Alt(s.head, r)
}

ghost predicate HasFiniteHeight_Alt(t: Tree)
{
  forall r :: 
    ValidPath_Alt(t, r) ==>
      !InfinitePath(r)
}

ghost function S2N(p: Stream<int>): CoOption<Number>
  decreases 0
{
  match p
  case Nil =>
    None
  case Cons(n, tail) =>
    Some(S2N'(if n < 0 then 0 else n, tail))
}

ghost function S2N'(n: nat, tail: Stream<int>): Number
  decreases n + 1
{
  if n <= 0 then
    Zero(S2N(tail))
  else
    Succ(S2N'(n - 1, tail))
}

ghost function N2S(r: CoOption<Number>): Stream<int>
{
  match r
  case None =>
    Nil
  case Some(num) =>
    N2S'(0, num)
}

ghost function N2S'(n: nat, num: Number): Stream<int>
  decreases num
{
  match num
  case Zero(r) =>
    Cons(n, N2S(r))
  case Succ(next) =>
    N2S'(n + 1, next)
}

lemma Path_Lemma0(t: Tree, p: Stream<int>)
  requires ValidPath(t, p)
  ensures ValidPath_Alt(t, S2N(p))
{
  if ValidPath(t, p) {
    Path_Lemma0'(t, p);
  }
}

greatest lemma Path_Lemma0'(t: Tree, p: Stream<int>)
  requires ValidPath(t, p)
  ensures ValidPath_Alt(t, S2N(p))
{
  match p {
    case {:split false} Nil =>
      assert t == Node(Nil);
    case {:split false} Cons(index, tail) =>
      assert 0 <= index;
      var ch := Tail(t.children, index);
      assert ch.Cons? && ValidPath(ch.head, tail);
      calc {
        ValidPath_Alt#[_k](t, S2N(p));
        {
          assert S2N(p) == Some(S2N'(index, tail));
        }
        ValidPath_Alt#[_k](t, Some(S2N'(index, tail)));
        ValidPath_Alt'#[_k - 1](t.children, S2N'(index, tail));
        {
          Path_Lemma0''(t.children, index, tail);
        }
        true;
      }
  }
}

greatest lemma Path_Lemma0''(tChildren: Stream<Tree>, n: nat, tail: Stream<int>)
  requires var ch := Tail(tChildren, n); ch.Cons? && ValidPath(ch.head, tail)
  ensures ValidPath_Alt'(tChildren, S2N'(n, tail))
{
  Tail_Lemma1(tChildren, 0, n);
  match S2N'(n, tail) {
    case {:split false} Succ(next) =>
      calc {
        Tail(tChildren, n);
        {
          Tail_Lemma1(tChildren, n - 1, n);
        }
        Tail(tChildren, n - 1).tail;
        {
          Tail_Lemma0(tChildren, n - 1);
        }
        Tail(tChildren.tail, n - 1);
      }
      Path_Lemma0''(tChildren.tail, n - 1, tail);
    case {:split false} Zero(r) =>
      Path_Lemma0'(tChildren.head, tail);
  }
}

lemma Path_Lemma1(t: Tree, r: CoOption<Number>)
  requires ValidPath_Alt(t, r)
  ensures ValidPath(t, N2S(r))
{
  if ValidPath_Alt(t, r) {
    Path_Lemma1'(t, r);
  }
}

greatest lemma Path_Lemma1'(t: Tree, r: CoOption<Number>)
  requires ValidPath_Alt(t, r)
  ensures ValidPath(t, N2S(r))
  decreases 1
{
  match r {
    case {:split false} None =>
      assert t == Node(Nil);
      assert N2S(r) == Nil;
    case {:split false} Some(num) =>
      assert ValidPath_Alt'(t.children, num);
      var p := N2S'(0, num);
      calc {
        ValidPath#[_k](t, N2S(r));
        ValidPath#[_k](t, N2S(Some(num)));
        ValidPath#[_k](t, N2S'(0, num));
        {
          Path_Lemma1''#[_k](t.children, 0, num);
        }
        true;
      }
  }
}

greatest lemma Path_Lemma1''(s: Stream<Tree>, n: nat, num: Number)
  requires ValidPath_Alt'(Tail(s, n), num)
  ensures ValidPath(Node(s), N2S'(n, num))
  decreases 0, num
{
  match num {
    case {:split false} Succ(next) =>
      Path_Lemma1''#[_k](s, n + 1, next);
    case {:split false} Zero(r) =>
      calc {
        ValidPath#[_k](Node(s), N2S'(n, num));
        ValidPath#[_k](Node(s), Cons(n, N2S(r)));
        Tail(s, n).Cons? &&
        ValidPath#[_k - 1](Tail(s, n).head, N2S(r));
        {
          assert Tail(s, n).Cons?;
        }
        ValidPath#[_k - 1](Tail(s, n).head, N2S(r));
        {
          Path_Lemma1'(Tail(s, n).head, r);
        }
        true;
      }
  }
}

lemma Path_Lemma2(p: Stream<int>)
  ensures IsNeverEndingStream(p) ==> InfinitePath(S2N(p))
{
  if IsNeverEndingStream(p) {
    Path_Lemma2'(p);
  }
}

greatest lemma Path_Lemma2'(p: Stream<int>)
  requires IsNeverEndingStream(p)
  ensures InfinitePath(S2N(p))
{
  match p {
    case {:split false} Cons(n, tail) =>
      calc {
        InfinitePath#[_k](S2N(p));
        InfinitePath#[_k](Some(S2N'(if n < 0 then 0 else n, tail)));
        InfinitePath'#[_k - 1](S2N'(if n < 0 then 0 else n, tail));
      <==
        {
          Path_Lemma2''(p, if n < 0 then 0 else n, tail);
        }
        InfinitePath#[_k - 1](S2N(tail));
        {
          Path_Lemma2'(tail);
        }
        true;
      }
  }
}

greatest lemma Path_Lemma2''(p: Stream<int>, n: nat, tail: Stream<int>)
  requires IsNeverEndingStream(p) && p.tail == tail
  ensures InfinitePath'(S2N'(n, tail))
{
  Path_Lemma2'(tail);
}

lemma Path_Lemma3(r: CoOption<Number>)
  ensures InfinitePath(r) ==> IsNeverEndingStream(N2S(r))
{
  if InfinitePath(r) {
    match r {
      case {:split false} Some(num) =>
        Path_Lemma3'(0, num);
    }
  }
}

greatest lemma Path_Lemma3'(n: nat, num: Number)
  requires InfinitePath'(num)
  ensures IsNeverEndingStream(N2S'(n, num))
  decreases num
{
  match num {
    case {:split false} Zero(r) =>
      calc {
        IsNeverEndingStream#[_k](N2S'(n, num));
        IsNeverEndingStream#[_k](Cons(n, N2S(r)));
        IsNeverEndingStream#[_k - 1](N2S(r));
        {
          Path_Lemma3'(0, r.get);
        }
        true;
      }
    case {:split false} Succ(next) =>
      Path_Lemma3'#[_k](n + 1, next);
  }
}

lemma Theorem2(t: Tree)
  ensures HasFiniteHeight(t) <==> HasFiniteHeight_Alt(t)
{
  if HasFiniteHeight_Alt(t) {
    forall p | true {
      calc ==> {
        ValidPath(t, p);
        {
          Path_Lemma0(t, p);
        }
        ValidPath_Alt(t, S2N(p));
        !InfinitePath(S2N(p));
        {
          Path_Lemma2(p);
        }
        !IsNeverEndingStream(p);
      }
    }
  }
  if HasFiniteHeight(t) {
    forall r | true {
      calc ==> {
        ValidPath_Alt(t, r);
        {
          Path_Lemma1(t, r);
        }
        ValidPath(t, N2S(r));
        !IsNeverEndingStream(N2S(r));
        {
          Path_Lemma3(r);
        }
        !InfinitePath(r);
      }
    }
  }
}

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

datatype Tree = Node(children: Stream<Tree>)

codatatype CoOption<T> = None | Some(get: T)

datatype Number = Succ(Number) | Zero(CoOption<Number>)

codatatype InfPath = Right(InfPath) | Down(InfPath) | Stop

codatatype FinPath = Right(FinPath) | Down(FinPath) | Stop
