
// SchorrWaite-stages.dfy


abstract module M0 {
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
    decreases *
  {
    root.marked := true;
    var t, p: Node? := root, null;
    ghost var stackNodes: seq<Node> := [];
    while true
      invariant forall i :: 0 <= i < |stackNodes| ==> stackNodes[i] in S
      invariant t in S && t !in stackNodes
      invariant p == if |stackNodes| == 0 then null else stackNodes[|stackNodes| - 1]
      invariant forall n :: n in stackNodes ==> n.childrenVisited < |n.children|
      invariant t.childrenVisited <= |t.children|
      invariant forall n :: n in S && n !in stackNodes && n != t ==> n.childrenVisited == 0
      invariant forall n :: n in stackNodes ==> |n.children| == old(|n.children|) && forall j :: 0 <= j < |n.children| ==> j == n.childrenVisited || n.children[j] == old(n.children[j])
      invariant forall n :: n in S && n !in stackNodes ==> n.children == old(n.children)
      invariant 0 < |stackNodes| ==> stackNodes[0].children[stackNodes[0].childrenVisited] == null
      invariant forall k {:matchinglooprewrite false} :: 0 < k < |stackNodes| ==> stackNodes[k].children[stackNodes[k].childrenVisited] == stackNodes[k - 1]
      invariant forall k {:matchinglooprewrite false} :: 0 <= k < |stackNodes| - 1 ==> old(stackNodes[k].children)[stackNodes[k].childrenVisited] == stackNodes[k + 1]
      invariant 0 < |stackNodes| ==> old(stackNodes[|stackNodes| - 1].children)[stackNodes[|stackNodes| - 1].childrenVisited] == t
      decreases *
    {
      if t.childrenVisited == |t.children| {
        t.childrenVisited := 0;
        if p == null {
          break;
        }
        t, p, p.children := p, p.children[p.childrenVisited], p.children[p.childrenVisited := t];
        stackNodes := stackNodes[..|stackNodes| - 1];
        t.childrenVisited := t.childrenVisited + 1;
      } else if t.children[t.childrenVisited] == null || t.children[t.childrenVisited].marked {
      } else {
        stackNodes := stackNodes + [t];
        t, p, t.children := t.children[t.childrenVisited], t, t.children[t.childrenVisited := p];
        t.marked := true;
        assume t !in stackNodes;
      }
    }
    assume root.marked && forall n :: n in S && n.marked ==> forall ch :: ch in n.children && ch != null ==> ch.marked;
    assume forall n :: n in S && n.marked ==> old(Reachable(root, n, S));
  }

  class Node {
    var children: seq<Node?>
    var marked: bool
    var childrenVisited: nat
  }

  datatype Path = Empty | Extend(Path, Node)
}

abstract module M1 refines M0 {
  method SchorrWaite ...
  {
    ...;
    while ...
      invariant root.marked
      invariant forall n :: n in S && n.marked && n !in stackNodes && n != t ==> forall ch :: ch in n.children && ch != null ==> ch.marked
      invariant forall n :: n in stackNodes || n == t ==> n.marked && forall j :: 0 <= j < n.childrenVisited ==> n.children[j] == null || n.children[j].marked
    {
      if ... {
      } else if ... {
      } else {
        ...;
        assert ...;
      }
    }
    assert ...;
    assume ...;
  }
}

abstract module M2 refines M1 {
  method SchorrWaite ...
  {
    ghost var path := Path.Empty;
    root.pathFromRoot := path;
    ...;
    while ...
      invariant old(allocated(path)) && old(ReachableVia(root, path, t, S))
      invariant forall n :: n in S && n.marked ==> var pth := n.pathFromRoot; old(allocated(pth)) && old(ReachableVia(root, pth, n, S))
      invariant forall n :: n in S && n.marked ==> old(Reachable(root, n, S))
    {
      if ... {
        ...;
        path := t.pathFromRoot;
      } else if ... {
      } else {
        path := Path.Extend(path, t);
        ...;
        t.pathFromRoot := path;
      }
    }
    assert ...;
    assert ...;
  }

  class Node ... {
    ghost var pathFromRoot: Path
  }
}

module M3 refines M2 {
  method SchorrWaite ...
    decreases true
  {
    ghost var unmarkedNodes := S - {root};
    ...;
    while ...
      invariant forall n :: n in S && !n.marked ==> n in unmarkedNodes
      decreases unmarkedNodes, stackNodes, |t.children| - t.childrenVisited
    {
      if ... {
      } else if ... {
      } else {
        ...;
        unmarkedNodes := unmarkedNodes - {t};
      }
    }
  }
}
