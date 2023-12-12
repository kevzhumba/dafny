
// MonotonicHeapstate.dfy


module M0 {
  datatype Kind = Constant | Ident | Binary

  class Expr {
    var kind: Kind
    var value: int
    var left: Expr?
    var right: Expr?
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      Core() &&
      Valid'()
    }

    ghost predicate Core()
      reads this, Repr
      decreases Repr, 0
    {
      this in Repr &&
      (left != null ==>
        left in Repr &&
        this !in left.Repr &&
        right !in left.Repr &&
        left.Repr <= Repr &&
        left.Valid()) &&
      (right != null ==>
        right in Repr &&
        this !in right.Repr &&
        left !in right.Repr &&
        right.Repr <= Repr &&
        right.Valid()) &&
      (kind == Binary ==>
        left != null &&
        right != null &&
        left.Repr !! right.Repr)
    }

    ghost predicate Valid'()
      requires Core()
      reads this, Repr
      decreases Repr, 1

    constructor CreateConstant(x: int)
      ensures Valid() && fresh(Repr)
    {
      kind, value := Constant, x;
      left, right := null, null;
      Repr := {this};
      new;
      assume Valid'();
    }

    constructor CreateIdent(name: int)
      ensures Valid() && fresh(Repr)
    {
      kind, value := Ident, name;
      left, right := null, null;
      Repr := {this};
      new;
      assume Valid'();
    }

    constructor CreateBinary(op: int, left: Expr, right: Expr)
      requires left.Valid()
      requires right.Valid()
      requires left.Repr !! right.Repr
      ensures Valid() && fresh(Repr - left.Repr - right.Repr)
    {
      kind, value := Binary, op;
      this.left, this.right := left, right;
      Repr := {this} + left.Repr + right.Repr;
      new;
      assume Valid'();
    }
  }
}

module M1 refines M0 {
  class Expr ... {
    ghost var resolved: bool

    ghost predicate Valid' ...
    {
      (resolved ==>
        kind == Binary ==>
          left.resolved &&
          right.resolved) &&
      Valid''()
    }

    ghost predicate Valid''()
      reads this, Repr
      ensures !resolved ==> Valid''()

    constructor CreateConstant ...
    {
      resolved := false;
      new;
      assert ...;
    }

    constructor CreateIdent ...
    {
      resolved := false;
      new;
      assert ...;
    }

    constructor CreateBinary ...
    {
      resolved := false;
      new;
      assert ...;
    }

    method Resolve()
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures resolved
      decreases Repr
    {
      if kind == Binary {
        left.Resolve();
        right.Resolve();
      }
      Repr := Repr + (if left != null then left.Repr else {}) + if right != null then right.Repr else {};
      resolved := true;
      assume Valid'();
    }
  }
}

module M2 refines M1 {
  class VarDecl { }

  class Expr ... {
    var decl: VarDecl?

    ghost predicate Valid'' ...
    {
      resolved ==>
        kind == Ident ==>
          decl != null
    }

    method Resolve ...
    {
      if kind != Ident {
        decl := new VarDecl;
      }
      ...;
      assert ...;
    }
  }
}

module M3 refines M2 {
  class VarDecl ... {
    var val: int
  }

  class Expr ... {
    method Eval() returns (r: int)
      requires Valid()
      requires resolved
      decreases Repr
    {
      match kind {
        case {:split false} Constant =>
          r := value;
        case {:split false} Ident =>
          r := decl.val;
        case {:split false} Binary =>
          var x := left.Eval();
          var y := right.Eval();
          r := x + y;
      }
    }
  }
}
