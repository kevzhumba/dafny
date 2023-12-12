
// SchorrWaite.dfy

method RecursiveMark(root: Node, ghost S: set<Node>)
  requires root in S
  requires forall n :: n in S ==> forall ch :: ch in n.children ==> ch == null || ch in S
  requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
  modifies S
  ensures root.marked
  ensures forall n :: n in S && n.marked ==> forall ch :: ch in n.children && ch != null ==> ch.marked
  ensures forall n :: n in S ==> n.childrenVisited == old(n.childrenVisited) && n.children == old(n.children)
{
}

method RecursiveMarkWorker(root: Node, ghost S: set<Node>, ghost stackNodes: set<Node>)
  requires root in S
  requires forall n :: n in S ==> forall ch :: ch in n.children ==> ch == null || ch in S
  requires forall n :: n in S && n.marked ==> n in stackNodes || forall ch :: ch in n.children && ch != null ==> ch.marked
  requires forall n :: n in stackNodes ==> n.marked
  modifies S
  ensures root.marked
  ensures forall n :: n in S && n.marked ==> n in stackNodes || forall ch :: ch in n.children && ch != null ==> ch.marked
  ensures forall n :: n in S && old(n.marked) ==> n.marked
  ensures forall n :: n in S ==> n.childrenVisited == old(n.childrenVisited) && n.children == old(n.children)
  decreases S - stackNodes
{
  if !root.marked {
    root.marked := true;
    var i := 0;
    while i < |root.children|
      invariant root.marked && i <= |root.children|
      invariant forall n :: n in S && n.marked ==> n == root || n in stackNodes || forall ch :: ch in n.children && ch != null ==> ch.marked
      invariant forall j :: 0 <= j < i ==> root.children[j] == null || root.children[j].marked
      invariant forall n :: n in S && old(n.marked) ==> n.marked
      invariant forall n :: n in S ==> n.childrenVisited == old(n.childrenVisited) && n.children == old(n.children)
    {
      var c := root.children[i];
      if c != null {
        RecursiveMarkWorker(c, S, stackNodes + {root});
      }
      i := i + 1;
    }
  }
}

method IterativeMark(root: Node, ghost S: set<Node>)
  requires root in S
  requires forall n :: n in S ==> forall ch :: ch in n.children ==> ch == null || ch in S
  requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
  modifies S
  ensures root.marked
  ensures forall n :: n in S && n.marked ==> forall ch :: ch in n.children && ch != null ==> ch.marked
  ensures forall n :: n in S ==> n.childrenVisited == old(n.childrenVisited) && n.children == old(n.children)
{
  var t := root;
  t.marked := true;
  var stackNodes: seq<Node> := [];
  ghost var unmarkedNodes := S - {t};
  while true
    invariant root.marked && t in S && t !in stackNodes
    invariant forall i, j :: 0 <= i < j < |stackNodes| ==> stackNodes[i] != stackNodes[j]
    invariant forall n :: n in stackNodes ==> n in S
    invariant forall n :: n in stackNodes || n == t ==> n.marked && 0 <= n.childrenVisited <= |n.children| && forall j :: 0 <= j < n.childrenVisited ==> n.children[j] == null || n.children[j].marked
    invariant forall n :: n in stackNodes ==> n.childrenVisited < |n.children|
    invariant forall j :: 0 <= j && j + 1 < |stackNodes| ==> stackNodes[j].children[stackNodes[j].childrenVisited] == stackNodes[j + 1]
    invariant 0 < |stackNodes| ==> stackNodes[|stackNodes| - 1].children[stackNodes[|stackNodes| - 1].childrenVisited] == t
    invariant forall n :: n in S && n.marked && n !in stackNodes && n != t ==> forall ch :: ch in n.children && ch != null ==> ch.marked
    invariant forall n :: n in S && n !in stackNodes && n != t ==> n.childrenVisited == old(n.childrenVisited)
    invariant forall n :: n in S ==> n.children == old(n.children)
    invariant forall n :: n in S && !n.marked ==> n in unmarkedNodes
    decreases unmarkedNodes, stackNodes, |t.children| - t.childrenVisited
  {
    if t.childrenVisited == |t.children| {
      assert {:focus} true;
      t.childrenVisited := 0;
      if |stackNodes| == 0 {
        return;
      }
      t := stackNodes[|stackNodes| - 1];
      stackNodes := stackNodes[..|stackNodes| - 1];
      t.childrenVisited := t.childrenVisited + 1;
    } else if t.children[t.childrenVisited] == null || t.children[t.childrenVisited].marked {
      t.childrenVisited := t.childrenVisited + 1;
    } else {
      assert {:focus} true;
      stackNodes := stackNodes + [t];
      t := t.children[t.childrenVisited];
      t.marked := true;
      unmarkedNodes := unmarkedNodes - {t};
    }
  }
}

ghost predicate Reachable(source: Node, sink: Node, S: set<Node>)
  reads S
{
  exists via :: 
    ReachableVia(source, via, sink, S)
}

ghost predicate ReachableVia(source: Node, older p: Path, sink: Node, S: set<Node>)
  reads S
  decreases p
{
  match p
  case Empty =>
    source == sink
  case Extend(prefix, n) =>
    n in S &&
    sink in n.children &&
    ReachableVia(source, prefix, n, S)
}

method SchorrWaite(root: Node, ghost S: set<Node>)
  requires root in S
  requires forall n :: n in S ==> forall ch :: ch in n.children ==> ch == null || ch in S
  requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
  modifies S
  ensures root.marked
  ensures forall n :: n in S && n.marked ==> forall ch :: ch in n.children && ch != null ==> ch.marked
  ensures forall n :: n in S && n.marked ==> old(Reachable(root, n, S))
  ensures forall n :: n in S ==> n.childrenVisited == old(n.childrenVisited) && n.children == old(n.children)
{
  var t := root;
  var p: Node? := null;
  ghost var path := Path.Empty;
  t.marked := true;
  t.pathFromRoot := path;
  ghost var stackNodes: seq<Node> := [];
  ghost var unmarkedNodes := S - {t};
  while true
    invariant forall i :: 0 <= i < |stackNodes| ==> stackNodes[i] in S
    invariant t in S && t !in stackNodes
    invariant p == if |stackNodes| == 0 then null else stackNodes[|stackNodes| - 1]
    invariant forall n :: n in stackNodes ==> n.childrenVisited < |n.children|
    invariant t.childrenVisited <= |t.children|
    invariant forall n :: n in S && n !in stackNodes && n != t ==> n.childrenVisited == 0
    invariant forall n :: n in stackNodes ==> |n.children| == old(|n.children|) && forall j :: 0 <= j < |n.children| ==> j == n.childrenVisited || n.children[j] == old(n.children[j])
    invariant forall n :: n in S && n !in stackNodes ==> n.children == old(n.children)
    invariant 0 < |stackNodes| ==> stackNodes[0].children[assert stackNodes[0] in stackNodes; assert stackNodes[0].childrenVisited < |stackNodes[0].children|; stackNodes[0].childrenVisited] == null
    invariant forall k {:matchinglooprewrite false} :: 0 < k < |stackNodes| ==> stackNodes[k].children[stackNodes[k].childrenVisited] == stackNodes[k - 1]
    invariant forall k {:matchinglooprewrite false} :: 0 <= k < |stackNodes| - 1 ==> old(stackNodes[k].children)[stackNodes[k].childrenVisited] == stackNodes[k + 1]
    invariant 0 < |stackNodes| ==> old(stackNodes[|stackNodes| - 1].children)[stackNodes[|stackNodes| - 1].childrenVisited] == t
    invariant root.marked
    invariant forall n :: n in S && n.marked && n !in stackNodes && n != t ==> forall ch :: ch in n.children && ch != null ==> ch.marked
    invariant forall n :: n in stackNodes || n == t ==> n.marked && forall j :: 0 <= j < n.childrenVisited ==> n.children[j] == null || n.children[j].marked
    invariant old(allocated(path)) && old(ReachableVia(root, path, t, S))
    invariant forall n :: n in S && n.marked ==> var pth := n.pathFromRoot; old(allocated(pth)) && old(ReachableVia(root, pth, n, S))
    invariant forall n :: n in S && n.marked ==> old(Reachable(root, n, S))
    invariant forall n :: n in S && !n.marked ==> n in unmarkedNodes
    decreases unmarkedNodes, stackNodes, |t.children| - t.childrenVisited
  {
    if t.childrenVisited == |t.children| {
      assert {:focus} true;
      t.childrenVisited := 0;
      if p == null {
        return;
      }
      var oldP := p.children[p.childrenVisited];
      p.children := p.children[p.childrenVisited := t];
      t := p;
      p := oldP;
      stackNodes := stackNodes[..|stackNodes| - 1];
      t.childrenVisited := t.childrenVisited + 1;
      path := t.pathFromRoot;
    } else if t.children[t.childrenVisited] == null || t.children[t.childrenVisited].marked {
      assert {:focus} true;
      t.childrenVisited := t.childrenVisited + 1;
    } else {
      assert {:focus} true;
      var newT := t.children[t.childrenVisited];
      t.children := t.children[t.childrenVisited := p];
      p := t;
      stackNodes := stackNodes + [t];
      path := Path.Extend(path, t);
      t := newT;
      t.marked := true;
      t.pathFromRoot := path;
      unmarkedNodes := unmarkedNodes - {t};
    }
  }
}

class Node {
  var children: seq<Node?>
  var marked: bool
  var childrenVisited: nat
  ghost var pathFromRoot: Path
}

datatype Path = Empty | Extend(Path, Node)
