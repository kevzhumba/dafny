include "../lib/seq.dfy"
include "../lib/binaryTree.dfy"
// DiameterOfBinaryTree.min.dfy


module TreeDiameter {
  method TestPath()
  {
    var rootleaf := Node(4, Nil, Nil);
    var leaf := Node(3, Nil, Nil);
    var child := Node(2, Nil, leaf);
    var root := Node(1, child, rootleaf);
    var test := Node(10, rootleaf, rootleaf);
    assert isTreePath([rootleaf, root, rootleaf], rootleaf, rootleaf);
    assert !isTreePath([root, rootleaf], leaf, rootleaf);
    assert isTreePath([leaf, child, root], leaf, root);
    assert isTreePath([root, rootleaf], root, rootleaf);
    assert isTreePath([leaf, child, root, rootleaf], leaf, rootleaf);
    assert isDescTreePath([root, child, leaf], root, leaf);
    assert !isDescTreePath([root], root, leaf);
    assert isDescTreePath([root, rootleaf], root, rootleaf);
    assert isTreePath([leaf, child, root], leaf, root);
    assert isTreePath([root, child, leaf], root, leaf);
  }

  ghost predicate isDiameter(path: seq<Tree>, start: Tree, end: Tree, root: Tree)
  {
    isPath(path, start, end, root) &&
    forall paths: seq<Tree>, pathStart: Tree, pathEnd: Tree :: 
      isPath(paths, pathStart, pathEnd, root) ==>
        |path| >= |paths|
  }

  ghost function tallestChild(root: Tree): Tree
  {
    if root == Nil then
      Nil
    else if root != Nil && TreeHeight(root.left) > TreeHeight(root.right) then
      root.left
    else
      root.right
  }


  lemma ascPathEndsAtRelativeRoot(start: Tree, end: Tree, path: seq<Tree>)
    requires start != Nil && end != Nil
    requires isAscTreePath(path, start, end)
    ensures isValidPath(path, end)
  {
    if |path| == 1 {
    } else {
      AscPathChildren(path, start, end);
      AscTreePathNotNil(path, start, end);
      assert isChild(end, path[|path| - 2]);
      assert path[|path| - 2] in path;
      assert path[|path| - 2] != Nil;
      assert path[|path| - 2] in TreeSet(end);
      AscTreePathSplit(path, start, end);
      ascPathEndsAtRelativeRoot(start, path[|path| - 2], path[..|path| - 1]);
    }
  }

  lemma pathEndingAtRootAsc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path && path[|path| - 1] == root && end == root
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires |path| >= 1
    ensures isAscTreePath(path, start, root)
    decreases |path|
  {
    if |path| == 1 {
    } else {
      TreePathNotNil(path, start, root);
      TreePathsReverseAreTreePaths(path, start, end);
      ReverseIndexAll(path);
      TreePathStartingAtRootIsDesc(reverse(path), end, start, root);
      DescPathIsAscPath(reverse(path), root, start);
      assert isAscTreePath(reverse(reverse(path)), start, root);
      reverseReverseIdempotent(path);
    }
  }

  lemma nonAscendingContra(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires path[|path| - 1] == root
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures false
  {
    assert end == root;
    if |path| == 1 {
      assert isAscTreePath(path, start, end);
      assert false;
    } else {
      if isChild(path[|path| - 2], path[|path| - 1]) {
        parentNotInTreeSet(path[|path| - 2], root);
      } else if isChild(path[|path| - 1], path[|path| - 2]) {
        if |path| == 2 {
        } else {
          TreePathsAreTheSameAlt(path, start, end);
          TreePathSplit(path, start, end);
          distinctSplits(path);
          if isAscTreePath(path[..|path| - 1], start, path[|path| - 2]) {
            assert path == path[..|path| - 1] + [root];
            AscTreePathNotNil(path[..|path| - 1], start, path[|path| - 2]);
            AscTreePathAreTheSame(path[..|path| - 1], start, path[|path| - 2]);
            assert isAscTreePathAlt(path, start, root);
            AscTreePathAreTheSameAlt(path, start, root);
            assert isAscTreePath(path, start, root);
            assert false;
          } else if isDescTreePath(path[..|path| - 1], start, path[|path| - 2]) {
            DescPathChildren(path[..|path| - 1], start, path[|path| - 2]);
            assert isChild(path[|path| - 3], path[|path| - 2]);
            parentsAreTheSame(path[|path| - 3], root, path[|path| - 2]);
            assert path[|path| - 3] == root;
            assert !distinct(path);
            assert false;
          } else {
            if isValidPath(path[..|path| - 1], path[|path| - 2]) {
              nonAscendingContra(path[|path| - 2], start, path[|path| - 2], path[..|path| - 1]);
            } else {
              var nextRoot := path[|path| - 2];
              assert TreeSet(nextRoot) <= TreeSet(root);
              TreePathsAreTheSameAlt(path, start, end);
              var badnode: Tree, k: nat :| badnode in path[..|path| - 1] && badnode !in TreeSet(nextRoot) && badnode in TreeSet(root) && k < |path| - 2 && path[k] == badnode;
              TreePathNotNil(path, start, end);
              if nextRoot == root.left {
                assert badnode in TreeSet(root.right);
                nonAscendingContraHelpLeft(root, start, end, path, k, |path| - 2, badnode);
                assert false;
              } else if nextRoot == root.right {
                assert badnode in TreeSet(root.left);
                nonAscendingContraHelpRight(root, start, end, path, k, |path| - 2, badnode);
                assert false;
              } else {
                assert false;
              }
            }
          }
        }
      } else {
        assert !isParentOrChild(path[|path| - 2], path[|path| - 1]);
        assert path == path[..|path| - 2] + [path[|path| - 2], root];
        TreePathsAreTheSameAlt(path, start, end);
        assert false;
      }
    }
  }

  lemma nonAscendingContraHelpRight(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: nat, i: nat, badnode: Tree)
    requires |path| > 2
    requires root != Nil
    requires root in path
    requires forall node :: node in path ==> node != Nil
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isTreePathAlt(path, start, end)
    requires path[|path| - 1] == root
    requires isChild(path[|path| - 1], path[|path| - 2])
    requires root.right == path[|path| - 2]
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    requires !isValidPath(path[..|path| - 1], path[|path| - 2])
    requires k < i <= |path| - 2
    requires path[i] in TreeSet(root.right)
    requires badnode in path[..|path| - 1]
    requires badnode !in TreeSet(root.right) && badnode !in TreeSet(path[i]) && badnode in TreeSet(root) && badnode in TreeSet(root.left)
    requires k < |path| - 2 && path[k] == badnode
    ensures false
    decreases i - k
  {
    if root.left == Nil {
    } else {
      assert badnode in path;
      assert path[i] in path;
      TreeSetChildInTreeSet(root.right, path[i]);
      TreeSetChildInTreeSet(root.left, badnode);
      if isChild(badnode, path[k + 1]) {
        assert path[k + 1] in TreeSet(badnode);
        TreeSetChildInTreeSet(badnode, path[k + 1]);
        assert path[k + 1] in TreeSet(root.left);
        assert TreeSet(path[i]) <= TreeSet(root.right);
        assert TreeSet(path[i]) !! TreeSet(path[k + 1]);
        nonAscendingContraHelpRight(root, start, end, path, k + 1, i, path[k + 1]);
      } else if isChild(path[k + 1], badnode) {
        if path[k + 1] in TreeSet(root.left) {
          nonAscendingContraHelpRight(root, start, end, path, k + 1, i, path[k + 1]);
        } else if path[k + 1] in TreeSet(root) && path[k + 1] !in TreeSet(root.left) && path[k + 1] !in TreeSet(root.right) {
          assert path[k + 1] == root;
        } else if path[k + 1] in TreeSet(root.right) {
          assert badnode in TreeSet(path[k + 1]);
          TreeSetChildInTreeSet(root.right, path[k + 1]);
          assert TreeSet(path[k + 1]) <= TreeSet(root.right);
          assert false;
        } else {
        }
      } else {
      }
    }
  }

  lemma nonAscendingContraHelpLeft(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: nat, i: nat, badnode: Tree)
    requires |path| > 2
    requires root != Nil
    requires root in path
    requires forall node :: node in path ==> node != Nil
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isTreePathAlt(path, start, end)
    requires path[|path| - 1] == root
    requires isChild(path[|path| - 1], path[|path| - 2])
    requires root.left == path[|path| - 2]
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    requires !isValidPath(path[..|path| - 1], path[|path| - 2])
    requires k < i <= |path| - 2
    requires path[i] in TreeSet(root.left)
    requires badnode in path[..|path| - 1]
    requires badnode !in TreeSet(root.left) && badnode !in TreeSet(path[i]) && badnode in TreeSet(root) && badnode in TreeSet(root.right)
    requires k < |path| - 2 && path[k] == badnode
    ensures false
    decreases i - k
  {
    if root.left == Nil {
    } else {
      assert badnode in path;
      assert path[i] in path;
      TreeSetChildInTreeSet(root.left, path[i]);
      TreeSetChildInTreeSet(root.right, badnode);
      if k == |path| - 3 {
        assert isParentOrChild(path[k], path[|path| - 2]);
        assert path[k] !in TreeSet(path[|path| - 2]);
        assert isChild(path[k], path[|path| - 2]);
        parentsAreTheSame(path[|path| - 3], root, path[|path| - 2]);
      } else {
        if isChild(badnode, path[k + 1]) {
          assert path[k + 1] in TreeSet(badnode);
          TreeSetChildInTreeSet(badnode, path[k + 1]);
          assert path[k + 1] in TreeSet(root.right);
          assert TreeSet(path[i]) <= TreeSet(root.left);
          assert TreeSet(path[i]) !! TreeSet(path[k + 1]);
          nonAscendingContraHelpLeft(root, start, end, path, k + 1, i, path[k + 1]);
        } else if isChild(path[k + 1], badnode) {
          if path[k + 1] in TreeSet(root.right) {
            nonAscendingContraHelpLeft(root, start, end, path, k + 1, i, path[k + 1]);
          } else if path[k + 1] in TreeSet(root) && path[k + 1] !in TreeSet(root.left) && path[k + 1] !in TreeSet(root.right) {
            assert path[k + 1] == root;
          } else if path[k + 1] in TreeSet(root.left) {
            assert badnode in TreeSet(path[k + 1]);
            TreeSetChildInTreeSet(root.left, path[k + 1]);
            assert false;
          } else {
          }
        } else {
        }
      }
    }
  }

  lemma pathOptions(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    ensures isAscTreePath(path, start, end) || isDescTreePath(path, start, end) || exists i :: 0 < i < |path| - 1 && path[i] == root && isAscTreePath(path[..i + 1], start, root) && isDescTreePath(path[i..], root, end)
    decreases |path|
  {
    if isAscTreePath(path, start, end) {
    } else if isDescTreePath(path, start, end) {
    } else {
      assert !isAscTreePath(path, start, end);
      assert !isDescTreePath(path, start, end);
      if path[0] == root {
        if |path| == 1 {
          assert exists i :: 0 <= i < |path| && path[i] == root && isAscTreePath(path[..i + 1], start, root) && isDescTreePath(path[i..], root, end);
        } else {
          assert isAscTreePath(path[..0 + 1], start, root);
          pathStartingAtRootDesc(root, start, end, path);
          assert false;
        }
      } else if path[|path| - 1] == root {
        nonAscendingContra(root, start, end, path);
        assert false;
      } else {
        assert root in path[1..];
        isPathSlices(path, start, end, root);
        var i :| 0 < i < |path| - 1 && path[i] == root;
        assert path[..i + 1][|path[..i + 1]| - 1] == root;
        assert path[i..][0] == root;
        assert isPath(path[..i + 1], start, path[i], root);
        assert isPath(path[i..], root, end, root);
        pathStartingAtRootDesc(root, path[i], end, path[i..]);
        pathEndingAtRootAsc(root, start, path[i], path[..i + 1]);
      }
    }
  }

  lemma rootPathAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures |path| <= 2 * h + 1
  {
    assert start in TreeSet(root);
    assert end in TreeSet(root);
    RootBounded(root, h);
    pathOptions(root, start, end, path);
    if isDescTreePath(path, start, end) {
      descRoot(root, start, end, path);
      TreeHeightToDescTreePath(root, h);
      var maxend: Tree, maxpath: seq<Tree> :| isLeaf(maxend) && maxend in TreeSet(root) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h + 1 && isValidPath(maxpath, root) && distinct(maxpath);
      TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
      assert |path| <= |maxpath|;
    } else if isAscTreePath(path, start, end) {
      ascRoot(root, start, end, path);
      assert end == root;
      AscPathIsDescPath(path, start, root);
      ReverseIndexAll(path);
      assert |reverse(path)| == |path|;
      TreeHeightToDescTreePath(root, h);
      var maxend: Tree, maxpath: seq<Tree> :| isLeaf(maxend) && maxend in TreeSet(root) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h + 1 && isValidPath(maxpath, root) && distinct(maxpath);
      TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
      assert |path| <= |maxpath|;
    } else if i :| 0 < i < |path| - 1 && path[i] == root && isAscTreePath(path[..i + 1], start, root) && isDescTreePath(path[i..], root, end) {
      ReverseIndexAll(path[..i + 1]);
      AscPathIsDescPath(path[..i + 1], start, root);
      TreeHeightToDescTreePath(root, h);
      var maxend: Tree, maxpath: seq<Tree> :| isLeaf(maxend) && maxend in TreeSet(root) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h + 1 && isValidPath(maxpath, root) && distinct(maxpath);
      TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
      assert |path[..i + 1]| <= h + 1;
      assert |path[i..]| <= h + 1;
      assert |path| == |reverse(path[..i + 1])| + |path[i + 1..]|;
      assert |path| <= h + 1 + h;
    }
  }

  lemma {:verify} pathsWithoutRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root !in path
    requires |path| > 1
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures isValidPath(path, root.left) || isValidPath(path, root.right)


  lemma DescPathAllValid(path: seq<Tree>, start: Tree, end: Tree)
    requires isDescTreePath(path, start, end)
    ensures isValidPath(path, start)
  {
  }

  lemma TreeSetTransitive(root: Tree, child: Tree, path: seq<Tree>)
    requires root != Nil && child != Nil
    requires child in TreeSet(root)
    requires isValidPath(path, child)
    ensures isValidPath(path, root)
  {
  }


  lemma childHeightIsLessThanPath(root: Tree, child: Tree, h: int, end: Tree)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires isChild(root, child)
    requires TreeHeight(child) <= h - 1
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, child, anyend) && isValidPath(rootedPath, child) && distinct(rootedPath) ==> |rootedPath| <= h
  {
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, child, anyend) && isValidPath(rootedPath, child) && distinct(rootedPath)
      ensures |rootedPath| <= h
    {
      if |rootedPath| <= h {
      } else if |rootedPath| > h {
        TreeHeightMax(child);
        EndDeterminesPath(rootedPath, child, anyend);
        if anyend in TreeSet(child.left) {
          if child.left == Nil {
            assert false;
          } else {
            childHeightIsLessThanPath(child, child.left, TreeHeight(child), anyend);
            assert forall childPaths: seq<Tree>, anyend: Tree :: isDescTreePath(childPaths, child.left, anyend) && isValidPath(childPaths, child.left) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
            assert rootedPath[1] == child.left;
            assert rootedPath == [child] + rootedPath[1..];
            isDescPathAndValidImpliesAllValid(rootedPath, child, anyend);
            assert isDescTreePath(rootedPath[1..], child.left, anyend);
            assert isValidPath(rootedPath[1..], child.left);
            assert |rootedPath[1..]| <= TreeHeight(child);
            assert false;
          }
        } else if anyend in TreeSet(child.right) {
          if child.right == Nil {
            assert false;
          } else {
            childHeightIsLessThanPath(child, child.right, TreeHeight(child), anyend);
            assert forall childPaths: seq<Tree>, anyend: Tree :: isDescTreePath(childPaths, child.right, anyend) && isValidPath(childPaths, child.right) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
            isDescPathAndValidImpliesAllValid(rootedPath, child, anyend);
            assert isDescTreePath(rootedPath[1..], child.right, anyend);
            assert false;
          }
        } else {
          assert anyend !in TreeSet(child.right) && anyend !in TreeSet(child.left);
          if anyend == child {
          } else {
            assert anyend !in TreeSet(child);
            assert false;
          }
        }
      }
    }
  }

  lemma TreeHeightToMaxDescTreePath(root: Tree, h: int, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires end != Nil && end in TreeSet(root)
    requires isDescTreePath(path, root, end) && |path| == h + 1 && isValidPath(path, root) && distinct(path)
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, root, anyend) && isValidPath(rootedPath, root) && distinct(rootedPath) ==> |rootedPath| <= |path|
  {
    TreeHeightMax(root);
    RootBounded(root, h);
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, root, anyend) && isValidPath(rootedPath, root) && distinct(rootedPath)
      ensures |rootedPath| <= |path|
    {
      assert rootedPath[0] == root;
      assert |rootedPath| >= 1;
      if |rootedPath| == 1 {
      } else {
        EndDeterminesPath(rootedPath, root, anyend);
        if anyend in TreeSet(root.left) {
          childHeightIsLessThanPath(root, root.left, h, anyend);
          assert forall childPaths: seq<Tree>, anyend: Tree :: isDescTreePath(childPaths, root.left, anyend) && isValidPath(childPaths, root.left) && distinct(childPaths) ==> |childPaths| <= h;
          isDescPathAndValidImpliesAllValid(rootedPath, root, anyend);
          assert isDescTreePath(rootedPath[1..], root.left, anyend);
          assert |rootedPath[1..]| <= h;
          assert |rootedPath| <= h + 1;
        } else if anyend in TreeSet(root.right) {
          childHeightIsLessThanPath(root, root.right, h, anyend);
          isDescPathAndValidImpliesAllValid(rootedPath, root, anyend);
          assert isDescTreePath(rootedPath[1..], root.right, anyend);
          assert |rootedPath[1..]| <= h;
          assert |rootedPath| <= h + 1;
        } else {
          if anyend == root {
          } else {
            assert anyend !in TreeSet(root);
            assert false;
          }
        }
      }
    }
  }

  lemma BothCases(root: Tree, left: Tree, right: Tree, h1: int, h2: int)
    requires root != Nil && left != Nil && right != Nil
    requires ChildrenAreSeparate(root)
    requires root.left == left && root.right == right
    requires TreeHeight(root.left) == h1
    requires TreeHeight(root.right) == h2
    ensures exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| == h1 + h2 + 3 && isValidPath(path, root) && distinct(path)
  {
    TreeHeightToDescTreePath(right, h2);
    var rpath: seq<Tree>, rend: Tree :| isLeaf(rend) && rend in TreeSet(right) && isDescTreePath(rpath, right, rend) && |rpath| == h2 + 1 && isValidPath(rpath, right) && distinct(rpath);
    assert rend in TreeSet(right);
    assert isDescTreePath([root] + rpath, root, rend);
    DescTreePathToPath(rpath, root.right, rend);
    TreeHeightToDescTreePath(left, h1);
    var lpath: seq<Tree>, lend: Tree :| isLeaf(lend) && lend in TreeSet(left) && isDescTreePath(lpath, left, lend) && |lpath| == h1 + 1 && isValidPath(lpath, left) && distinct(lpath);
    assert isDescTreePath([root] + lpath, root, lend);
    DescTreePathToPath(lpath, root.left, lend);
    parentNotInTreeSet(root, left);
    parentNotInTreeSet(root, right);
    assert root !in TreeSet(left);
    assert root !in TreeSet(right);
    assert lend in TreeSet(left);
    distincts([root], lpath);
    assert distinct([root] + lpath);
    reverseDistinct([root] + lpath);
    assert rend != lend;
    DescPlusDesc([root] + rpath, lend, root, [root] + lpath, rend);
    assert isTreePath(reverse([root] + lpath) + rpath, lend, rend);
    assert |[root] + lpath| == h1 + 2;
    ReverseIndexAll([root] + lpath);
    assert |[root] + lpath| == h1 + 2;
    assert |reverse([root] + lpath) + rpath| == h1 + h2 + 3;
    distincts(reverse([root] + lpath), rpath);
  }

  ghost predicate largestPath(path: seq<Tree>, root: Tree)
  {
    forall start: Tree, end: Tree, paths: seq<Tree> :: 
      distinct(paths) &&
      isTreePath(paths, start, end) &&
      isValidPath(paths, root) ==>
        |path| >= |paths|
  }

  ghost predicate largestPathStart(path: seq<Tree>, root: Tree)
  {
    forall end: Tree, paths: seq<Tree> :: 
      distinct(paths) &&
      isTreePath(paths, root, end) &&
      isValidPath(paths, root) ==>
        |path| >= |paths|
  }

  lemma lpR(root: Tree)
    requires root != Nil && root.left == Nil && root.right == Nil
    ensures largestPath([root], root)
  {
    assert distinct([root]);
    assert isValidPath([root], root);
    assert isTreePath([root], root, root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
      ensures |[root]| >= |paths|
    {
      if |paths| > 1 {
        assert paths[0] != paths[1];
        if isChild(paths[0], paths[1]) {
          if paths[0] == root {
            assert false;
          } else if paths[1] == root {
            parentNotInTreeSet(paths[0], root);
            assert false;
          } else {
            assert paths[0] !in TreeSet(root);
          }
        } else if isChild(paths[1], paths[0]) {
          if paths[0] == root {
            parentNotInTreeSet(paths[1], root);
            assert false;
          } else if paths[1] == root {
            parentNotInTreeSet(paths[0], root);
            assert false;
          }
        } else {
          assert false;
        }
      } else if |paths| == 0 {
      } else {
      }
    }
  }

  method diameter(root: Tree) returns (heightDim: (int, int))
    requires ChildrenAreSeparate(root)
    ensures root == Nil ==> heightDim == (-1, -1)
    ensures root != Nil && root.left == Nil && root.right == Nil ==> heightDim == (0, 0)
    ensures heightDim.0 == TreeHeight(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == heightDim.1 && isValidPath(path, root) && distinct(path)
  {
    if root == Nil {
      return (-1, -1);
    }
    if root.left == Nil && root.right == Nil {
      ghost var path := [root];
      assert isTreePath([root], root, root);
      lpR(root);
    }
    var leftDiameter := diameter(root.left);
    var rightDiameter := diameter(root.right);
    var height := max(leftDiameter.0, rightDiameter.0) + 1;
    var dim := leftDiameter.0 + rightDiameter.0 + 2;
    var maxDiameter := max(leftDiameter.1, max(rightDiameter.1, dim));
    if root.right != Nil && root.left != Nil {
      BothCases(root, root.left, root.right, leftDiameter.0, rightDiameter.0);
      ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1;
      ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1;
      ghost var start, end, path :| isTreePath(path, start, end) && |path| == leftDiameter.0 + rightDiameter.0 + 3 && distinct(path);
      if leftDiameter.1 > max(rightDiameter.1, dim) {
        assert maxDiameter == leftDiameter.1;
      } else if rightDiameter.1 > dim {
        assert maxDiameter == rightDiameter.1;
      } else {
        assert |path| >= |rightPath|;
        assert |path| >= |leftPath|;
        assert dim >= rightDiameter.1;
        assert dim >= leftDiameter.1;
        assert |path| - 1 == dim;
        assert maxDiameter == dim;
      }
    } else if root.right != Nil {
      ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root);
      TreeHeightToDescTreePath(root.right, rightDiameter.0);
      ghost var rpath: seq<Tree>, end: Tree :| end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.right) && isDescTreePath(rpath, root.right, end) && |rpath| == rightDiameter.0 + 1 && isValidPath(rpath, root.right) && distinct(rpath);
      assert isDescTreePath([root] + rpath, root, end);
      DescTreePathToPath([root] + rpath, root, end);
      assert |[root] + rpath| == rightDiameter.0 + 2;
      parentNotInTreeSet(root, root.right);
      assert distinct([root] + rpath);
      assert leftDiameter.0 == -1;
      assert leftDiameter.1 == -1;
      if leftDiameter.1 > max(rightDiameter.1, dim) {
        assert false;
      } else if rightDiameter.1 > dim {
        assert maxDiameter == rightDiameter.1;
      } else {
        assert dim >= rightDiameter.1;
        assert dim >= leftDiameter.1;
        calc {
          dim;
          leftDiameter.0 + rightDiameter.0 + 2;
          -1 + rightDiameter.0 + 2;
          rightDiameter.0 + 1;
        }
        assert maxDiameter == dim;
        assert |[root] + rpath| - 1 == dim;
      }
    } else if root.left != Nil {
      ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1;
      TreeHeightToDescTreePath(root.left, leftDiameter.0);
      ghost var lpath: seq<Tree>, end: Tree :| end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.left) && isDescTreePath(lpath, root.left, end) && |lpath| == leftDiameter.0 + 1 && isValidPath(lpath, root.left) && distinct(lpath);
      assert isDescTreePath([root] + lpath, root, end);
      DescTreePathToPath([root] + lpath, root, end);
      parentNotInTreeSet(root, root.left);
      assert distinct([root] + lpath);
      assert dim == leftDiameter.0 + 1;
      assert rightDiameter.0 == -1;
      assert rightDiameter.1 == -1;
      assert leftDiameter.1 >= 0;
      if leftDiameter.1 > max(rightDiameter.1, dim) {
        assert maxDiameter == leftDiameter.1;
      } else if rightDiameter.1 > dim {
        assert false;
      } else {
        assert dim >= rightDiameter.1;
        assert dim >= leftDiameter.1;
        assert maxDiameter == dim;
      }
    }
    return (height, maxDiameter);
  }

  method diameterOfBinaryTree(root: Tree) returns (maxDiameter: int)
    requires ChildrenAreSeparate(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == maxDiameter && isValidPath(path, root) && distinct(path)
  {
    var result := diameter(root);
    maxDiameter := result.1;
  }

  import opened BinaryTree

  import opened Seq
}
