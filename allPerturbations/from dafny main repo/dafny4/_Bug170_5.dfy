
// Bug170.dfy


module InductiveThings {
  ghost predicate P(x: int)

  ghost predicate Q(x: int)

  least predicate A(x: int)
  {
    P(x) || B(x + 1)
  }

  least predicate B(x: int)
  {
    Q(x) || A(x + 1)
  }

  least lemma AA(x: int)
    requires A(x)
  {
    if B(x + 1) {
      BB(x + 1);
    }
  }

  least lemma BB(x: int)
    requires B(x)
  {
    if A(x + 1) {
      AA(x + 1);
    }
  }
}

module CoThings {
  greatest predicate A(x: int)
  {
    B(x + 1)
  }

  greatest predicate B(x: int)
  {
    A(x + 1)
  }

  greatest lemma AA(x: int)
    ensures A(x)
  {
    assert B(x + 1);
  }

  greatest lemma BB(x: int)
    ensures B(x)
  {
    AA(x + 1);
    assert A(x + 1);
  }
}

module SingleThings {
  ghost predicate P(x: int)

  least predicate A(x: int)
  {
    P(x) || A(x + 1)
  }

  least lemma AA(x: int)
    requires A(x)
  {
    if A(x + 1) {
      AA(x + 1);
    }
  }
}
