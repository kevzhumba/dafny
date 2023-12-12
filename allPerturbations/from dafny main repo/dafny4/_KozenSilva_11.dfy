
// KozenSilva.dfy

greatest predicate LexLess[nat](s: Stream<int>, t: Stream<int>)
{
  s.hd <= t.hd &&
  (s.hd == t.hd ==>
    LexLess(s.tl, t.tl))
}

greatest lemma Theorem1_LexLess_Is_Transitive[nat](s: Stream<int>, t: Stream<int>, u: Stream<int>)
  requires LexLess(s, t) && LexLess(t, u)
  ensures LexLess(s, u)
{
  if s.hd == u.hd {
    Theorem1_LexLess_Is_Transitive(s.tl, t.tl, u.tl);
  }
}

greatest lemma Theorem1_LexLess_Is_Transitive_Automatic[nat](s: Stream<int>, t: Stream<int>, u: Stream<int>)
  requires LexLess(s, t) && LexLess(t, u)
  ensures LexLess(s, u)
{
}

ghost predicate NotLexLess(s: Stream<int>, t: Stream<int>)
{
  exists k: nat :: 
    NotLexLess'(k, s, t)
}

ghost predicate NotLexLess'(k: nat, s: Stream<int>, t: Stream<int>)
{
  if k == 0 then
    false
  else
    !(s.hd <= t.hd) || (s.hd == t.hd && NotLexLess'(k - 1, s.tl, t.tl))
}

lemma EquivalenceTheorem(s: Stream<int>, t: Stream<int>)
  ensures LexLess(s, t) <==> !NotLexLess(s, t)
{
  if !NotLexLess(s, t) {
    EquivalenceTheorem0(s, t);
  }
  if LexLess(s, t) {
    EquivalenceTheorem1(s, t);
  }
}

greatest lemma EquivalenceTheorem0[nat](s: Stream<int>, t: Stream<int>)
  requires !NotLexLess(s, t)
  ensures LexLess(s, t)
{
  EquivalenceTheorem0_Lemma(_k, s, t);
}

lemma EquivalenceTheorem0_Lemma(k: nat, s: Stream<int>, t: Stream<int>)
  requires !NotLexLess'(k, s, t)
  ensures LexLess#[k](s, t)
{
}

lemma EquivalenceTheorem1(s: Stream<int>, t: Stream<int>)
  requires LexLess(s, t)
  ensures !NotLexLess(s, t)
{
  forall k: nat | true {
    EquivalenceTheorem1_Lemma(k, s, t);
  }
}

lemma EquivalenceTheorem1_Lemma(k: nat, s: Stream<int>, t: Stream<int>)
  requires LexLess(s, t)
  ensures !NotLexLess'(k, s, t)
{
}

lemma Theorem1_Alt(s: Stream<int>, t: Stream<int>, u: Stream<int>)
  requires NotLexLess(s, u)
  ensures NotLexLess(s, t) || NotLexLess(t, u)
{
  forall k: nat | NotLexLess'(k, s, u) {
    Theorem1_Alt_Lemma(k, s, t, u);
  }
}

lemma Theorem1_Alt_Lemma(k: nat, s: Stream<int>, t: Stream<int>, u: Stream<int>)
  requires NotLexLess'(k, s, u)
  ensures NotLexLess'(k, s, t) || NotLexLess'(k, t, u)
{
}

ghost function PointwiseAdd(s: Stream<int>, t: Stream<int>): Stream<int>
{
  Cons(s.hd + t.hd, PointwiseAdd(s.tl, t.tl))
}

greatest lemma Theorem2_Pointwise_Addition_Is_Monotone[nat](s: Stream<int>, t: Stream<int>, u: Stream<int>, v: Stream<int>)
  requires LexLess(s, t) && LexLess(u, v)
  ensures LexLess(PointwiseAdd(s, u), PointwiseAdd(t, v))
{
}

greatest predicate Subtype(a: RecType, b: RecType)
{
  a == Bottom || b == Top || (a.Arrow? && b.Arrow? && Subtype(b.dom, a.dom) && Subtype(a.ran, b.ran))
}

greatest lemma Theorem3_Subtype_Is_Transitive(a: RecType, b: RecType, c: RecType)
  requires Subtype(a, b) && Subtype(b, c)
  ensures Subtype(a, c)
{
}

greatest predicate ClEnvBelow[nat](c: ClEnv, d: ClEnv)
{
  forall y :: 
    y in c.m ==>
      y in d.m &&
      ValBelow(c.m[y], d.m[y])
}

greatest predicate ValBelow[nat](u: Val, v: Val)
{
  (u.ValConst? && v.ValConst? && u == v) || (u.ValCl? && v.ValCl? && u.cl.abs == v.cl.abs && ClEnvBelow(u.cl.env, v.cl.env))
}

greatest lemma Theorem4a_ClEnvBelow_Is_Transitive[nat](c: ClEnv, d: ClEnv, e: ClEnv)
  requires ClEnvBelow(c, d) && ClEnvBelow(d, e)
  ensures ClEnvBelow(c, e)
{
}

greatest lemma Theorem4b_ValBelow_Is_Transitive[nat](u: Val, v: Val, w: Val)
  requires ValBelow(u, v) && ValBelow(v, w)
  ensures ValBelow(u, w)
{
  if u.ValCl? {
    Theorem4a_ClEnvBelow_Is_Transitive(u.cl.env, v.cl.env, w.cl.env);
  }
}

ghost predicate IsCapsule(cap: Capsule)
{
  cap.e.TermAbs?
}

ghost function ClosureConversion(cap: Capsule): Cl
  requires IsCapsule(cap)
{
  Closure(cap.e.abs, ClosureConvertedMap(cap.s))
}

ghost function ClosureConvertedMap(s: map<Var, ConstOrAbs>): ClEnv
{
  ClEnvironment(map y: Var | y in s :: if s[y].AA? then ValCl(Closure(s[y].abs, ClosureConvertedMap(s))) else ValConst(s[y].c))
}

ghost predicate CapsuleEnvironmentBelow(s: map<Var, ConstOrAbs>, t: map<Var, ConstOrAbs>)
{
  forall y :: 
    y in s ==>
      y in t &&
      s[y] == t[y]
}

greatest lemma Theorem5_ClosureConversion_Is_Monotone[nat](s: map<Var, ConstOrAbs>, t: map<Var, ConstOrAbs>)
  requires CapsuleEnvironmentBelow(s, t)
  ensures ClEnvBelow(ClosureConvertedMap(s), ClosureConvertedMap(t))
{
}

greatest predicate Bisim(s: Stream, t: Stream)
{
  s.hd == t.hd &&
  Bisim(s.tl, t.tl)
}

greatest lemma Theorem6_Bisim_Is_Symmetric(s: Stream, t: Stream)
  requires Bisim(s, t)
  ensures Bisim(t, s)
{
}

ghost function merge(s: Stream, t: Stream): Stream
{
  Cons(s.hd, merge(t, s.tl))
}

ghost function SplitLeft(s: Stream): Stream
{
  Cons(s.hd, SplitRight(s.tl))
}

ghost function SplitRight(s: Stream): Stream
{
  SplitLeft(s.tl)
}

greatest lemma Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim(s: Stream)
  ensures Bisim(merge(SplitLeft(s), SplitRight(s)), s)
{
  var LHS := merge(SplitLeft(s), SplitRight(s));
  calc {
    Bisim#[_k](LHS, s);
  ==
    LHS.hd == s.hd &&
    Bisim#[_k - 1](LHS.tl, s.tl);
  ==
    calc {
      LHS.hd;
    ==
      merge(SplitLeft(s), SplitRight(s)).hd;
    ==
      SplitLeft(s).hd;
    ==
      s.hd;
    }
    Bisim#[_k - 1](LHS.tl, s.tl);
  ==
    calc {
      LHS.tl;
    ==
      merge(SplitLeft(s), SplitRight(s)).tl;
    ==
      merge(SplitRight(s), SplitLeft(s).tl);
    ==
      merge(SplitLeft(s.tl), SplitRight(s.tl));
    }
    Bisim#[_k - 1](merge(SplitLeft(s.tl), SplitRight(s.tl)), s.tl);
  ==
    {
      Theorem7_Merge_Is_Left_Inverse_Of_Split_Bisim(s.tl);
    }
    true;
  }
}

greatest lemma Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal(s: Stream)
  ensures merge(SplitLeft(s), SplitRight(s)) == s
{
  calc {
    merge(SplitLeft(s), SplitRight(s)).hd;
  ==
    SplitLeft(s).hd;
  ==
    s.hd;
  }
  calc {
    merge(SplitLeft(s), SplitRight(s)).tl;
  ==
    merge(SplitRight(s), SplitLeft(s).tl);
  ==
    merge(SplitLeft(s.tl), SplitRight(s.tl));
  ==#[_k - 1]
    {
      Theorem7_Merge_Is_Left_Inverse_Of_Split_Equal(s.tl);
    }
    s.tl;
  }
}

codatatype Stream<A> = Cons(hd: A, tl: Stream)

codatatype RecType = Bottom | Top | Arrow(dom: RecType, ran: RecType)

type Const(!new)

type Var(==,!new)

datatype Term = TermConst(Const) | TermVar(Var) | TermAbs(abs: LambdaAbs)

datatype LambdaAbs = Fun(v: Var, body: Term)

codatatype Val = ValConst(Const) | ValCl(cl: Cl)

codatatype Cl = Closure(abs: LambdaAbs, env: ClEnv)

codatatype ClEnv = ClEnvironment(m: map<Var, Val>)

datatype Capsule = Cap(e: Term, s: map<Var, ConstOrAbs>)

datatype ConstOrAbs = CC(c: Const) | AA(abs: LambdaAbs)
