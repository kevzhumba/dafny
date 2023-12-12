
// UltraFilter.dfy

ghost predicate IsFilter(f: set<set<G>>, S: set<G>)
{
  (forall A, B :: 
    A in f &&
    A <= B ==>
      B in f) &&
  (forall C, D :: 
    C in f &&
    D in f ==>
      C * D in f) &&
  S in f &&
  {} !in f
}

ghost predicate IsUltraFilter(f: set<set<G>>, S: set<G>)
{
  IsFilter(f, S) &&
  forall g :: 
    IsFilter(g, S) &&
    f <= g ==>
      f == g
}

lemma Theorem(f: set<set<G>>, S: set<G>, M: set<G>, N: set<G>)
  requires IsUltraFilter(f, S)
  requires M + N in f
  ensures M in f || N in f
{
  if M !in f {
    var h := H(f, S, M);
    Lemma_FHOrdering(h, f, S, M);
  }
}

lemma H(f: set<set<G>>, S: set<G>, M: set<G>)
    returns (h: set<set<G>>)
  ensures forall X :: X in h <==> M + X in f
{
  h := set X, Y | Y in f && X <= Y && M + X == Y :: X;
  forall X | true {
    calc {
      X in h;
      exists Y :: 
        Y in f &&
        X <= Y &&
        M + X == Y;
      M + X in f;
    }
  }
}

lemma Lemma_HIsFilter(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
  requires IsFilter(f, S)
  requires forall X :: X in h <==> M + X in f
  requires M !in f
  ensures IsFilter(h, S)
{
  forall A, B | A in h && A <= B
    ensures B in h
  {
    assert M + A <= M + B;
  }
  forall C, D | C in h && D in h
    ensures C * D in h
  {
    assert (M + C) * (M + D) == M + C * D;
  }
  Lemma_H2(h, f, S, M);
  Lemma_H3(h, f, S, M);
}

lemma Lemma_H2(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
  requires IsFilter(f, S)
  requires forall X :: X in h <==> M + X in f
  ensures S in h
{
  assume M <= S;
  assert M + S == S;
}

lemma Lemma_H3(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
  requires IsFilter(f, S)
  requires forall X :: X in h <==> M + X in f
  requires M !in f
  ensures {} !in h
{
  assert M + {} == M;
}

lemma Lemma_FHOrdering(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
  requires IsFilter(f, S)
  requires forall X :: X in h <==> M + X in f
  requires IsFilter(h, S)
  ensures f <= h
{
  forall Y | Y in f
    ensures Y in h
  {
  }
}

type G(==,!new)
