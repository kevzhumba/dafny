
// WideTrees.dfy

ghost function BigTree(): Tree
{
  Node(BigTrees())
}

ghost function BigTrees(): Stream<Tree>
  decreases 0
{
  SCons(BigTree(), BigTrees())
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
  case SNil =>
    true
  case SCons(t, tail) =>
    1 <= n &&
    LowerThan(t.children, n - 1) &&
    LowerThan(tail, n)
}

ghost function SmallTree(n: nat): Tree
{
  Node(SmallTrees(n))
}

ghost function SmallTrees(n: nat): Stream<Tree>
  decreases -1
{
  if n == 0 then
    SNil
  else
    SCons(SmallTree(n - 1), SmallTrees(n))
}

lemma Theorem(n: nat)
  ensures HasBoundedHeight(SmallTree(n))
{
  Lemma(n);
}

greatest lemma Lemma(n: nat)
  ensures LowerThan(SmallTrees(n), n)
{
}

codatatype Stream<T> = SNil | SCons(head: T, tail: Stream)

datatype Tree = Node(children: Stream<Tree>)
