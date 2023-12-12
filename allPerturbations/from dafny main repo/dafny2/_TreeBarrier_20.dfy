
// TreeBarrier.dfy

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int

  ghost predicate validDown()
    reads this, desc
  {
    this !in desc &&
    left != right &&
    (right != null ==>
      right in desc &&
      left !in right.desc) &&
    (left != null ==>
      left in desc &&
      (right != null ==>
        desc == {left, right} + left.desc + right.desc) &&
      (right == null ==>
        desc == {left} + left.desc) &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==>
        desc == {right} + right.desc) &&
      (right == null ==>
        desc == {})) &&
    (right != null ==>
      right.validDown()) &&
    (blocked() ==>
      forall m :: 
        m in desc ==>
          m.blocked()) &&
    (after() ==>
      forall m :: 
        m in desc ==>
          m.blocked() || m.after())
  }

  ghost predicate validUp()
    reads this, anc
  {
    this !in anc &&
    (parent != null ==>
      parent in anc &&
      anc == {parent} + parent.anc &&
      parent.validUp()) &&
    (parent == null ==>
      anc == {}) &&
    (after() ==>
      forall m :: 
        m in anc ==>
          m.after())
  }

  ghost predicate valid()
    reads this, desc, anc
  {
    validUp() &&
    validDown() &&
    desc !! anc
  }

  ghost predicate before()
    reads this
  {
    !sense &&
    pc <= 2
  }

  ghost predicate blocked()
    reads this
  {
    sense
  }

  ghost predicate after()
    reads this
  {
    !sense &&
    3 <= pc
  }

  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
    decreases *
  {
    pc := 1;
    if left != null {
      while !left.sense
        invariant validDown()
        invariant valid()
        decreases *
        modifies left
      {
        left.sense := *;
        assume left.blocked() ==> forall m :: m in left.desc ==> m.blocked();
      }
    }
    if right != null {
      while !right.sense
        invariant validDown()
        invariant valid()
        decreases *
        modifies right
      {
        right.sense := *;
        assume right.blocked() ==> forall m :: m in right.desc ==> m.blocked();
      }
    }
    pc := 2;
    if parent != null {
      sense := true;
    }
    pc := 3;
    while sense
      invariant validUp()
      invariant valid()
      invariant left == old(left)
      invariant right == old(right)
      invariant sense ==> parent != null
      decreases *
      modifies this
    {
      sense := *;
      assume !sense ==> parent.after();
    }
    pc := 3;
    if left != null {
      left.sense := false;
    }
    pc := 5;
    if right != null {
      right.sense := false;
    }
    pc := 6;
  }
}
