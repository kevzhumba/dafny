
// NipkowKlein-chapter3.dfy

ghost function append(xs: List, ys: List): List
{
  match xs
  case Nil =>
    ys
  case Cons(x, tail) =>
    Cons(x, append(tail, ys))
}

ghost function aval(a: aexp, s: state): val
{
  match a
  case N(n) =>
    n
  case V(x) =>
    s(x)
  case Plus(a0, a1) =>
    aval(a0, s) + aval(a1, s)
}

lemma Example0()
{
  var y := aval(Plus(N(3), V("x")), x => 0);
  assert y == 3;
}

ghost function asimp_const(a: aexp): aexp
{
  match a
  case N(n) =>
    a
  case V(x) =>
    a
  case Plus(a0, a1) =>
    var as0, as1 := asimp_const(a0), asimp_const(a1);
    if as0.N? && as1.N? then
      N(as0.n + as1.n)
    else
      Plus(as0, as1)
}

lemma AsimpConst(a: aexp, s: state)
  ensures aval(asimp_const(a), s) == aval(a, s)
{
  forall a' | a' < a {
    AsimpConst(a', s);
  }
}

ghost function plus(a0: aexp, a1: aexp): aexp
{
  if a0.N? && a1.N? then
    N(a0.n + a1.n)
  else if a0.N? then
    if a0.n == 0 then
      a1
    else
      Plus(a0, a1)
  else if a1.N? then
    if a1.n == 0 then
      a0
    else
      Plus(a0, a1)
  else
    Plus(a0, a1)
}

lemma AvalPlus(a0: aexp, a1: aexp, s: state)
  ensures aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s)
{
}

ghost function asimp(a: aexp): aexp
{
  match a
  case N(n) =>
    a
  case V(x) =>
    a
  case Plus(a0, a1) =>
    plus(asimp(a0), asimp(a1))
}

lemma AsimpCorrect(a: aexp, s: state)
  ensures aval(asimp(a), s) == aval(a, s)
{
  forall a' | a' < a {
    AsimpCorrect(a', s);
  }
}

lemma ASimplInvolutive(a: aexp)
  ensures asimp(asimp(a)) == asimp(a)
{
}

ghost function bval(b: bexp, s: state): bool
{
  match b
  case Bc(v) =>
    v
  case Not(b) =>
    !bval(b, s)
  case And(b0, b1) =>
    bval(b0, s) &&
    bval(b1, s)
  case Less(a0, a1) =>
    aval(a0, s) < aval(a1, s)
}

ghost function not(b: bexp): bexp
{
  match b
  case Bc(b0) =>
    Bc(!b0)
  case Not(b0) =>
    b0
  case And(_ /* _v8 */, _ /* _v9 */) =>
    Not(b)
  case Less(_ /* _v10 */, _ /* _v11 */) =>
    Not(b)
}

ghost function and(b0: bexp, b1: bexp): bexp
{
  if b0.Bc? then
    if b0.v then
      b1
    else
      b0
  else if b1.Bc? then
    if b1.v then
      b0
    else
      b1
  else
    And(b0, b1)
}

ghost function less(a0: aexp, a1: aexp): bexp
{
  if a0.N? && a1.N? then
    Bc(a0.n < a1.n)
  else
    Less(a0, a1)
}

ghost function bsimp(b: bexp): bexp
{
  match b
  case Bc(v) =>
    b
  case Not(b0) =>
    not(bsimp(b0))
  case And(b0, b1) =>
    and(bsimp(b0), bsimp(b1))
  case Less(a0, a1) =>
    less(asimp(a0), asimp(a1))
}

lemma BsimpCorrect(b: bexp, s: state)
  ensures bval(bsimp(b), s) == bval(b, s)
{
  match b
  case {:split false} Bc(v) =>
  case {:split false} Not(b0) =>
    BsimpCorrect(b0, s);
  case {:split false} And(b0, b1) =>
    BsimpCorrect(b0, s);
    BsimpCorrect(b1, s);
  case {:split false} Less(a0, a1) =>
    AsimpCorrect(a0, s);
    AsimpCorrect(a1, s);
}

ghost function exec1(i: instr, s: state, stk: stack): stack
{
  match i
  case LOADI(n) =>
    Cons(n, stk)
  case LOAD(x) =>
    Cons(s(x), stk)
  case ADD =>
    if stk.Cons? && stk.tail.Cons? then
      var Cons(a1, Cons(a0, tail)) := stk;
      Cons(a0 + a1, tail)
    else
      Nil
}

ghost function exec(ii: List<instr>, s: state, stk: stack): stack
{
  match ii
  case Nil =>
    stk
  case Cons(i, rest) =>
    exec(rest, s, exec1(i, s, stk))
}

ghost function comp(a: aexp): List<instr>
{
  match a
  case N(n) =>
    Cons(LOADI(n), Nil)
  case V(x) =>
    Cons(LOAD(x), Nil)
  case Plus(a0, a1) =>
    append(append(comp(a0), comp(a1)), Cons(ADD, Nil))
}

lemma CorrectCompilation(a: aexp, s: state, stk: stack)
  ensures exec(comp(a), s, stk) == Cons(aval(a, s), stk)
{
}

lemma ExecAppend(ii0: List<instr>, ii1: List<instr>, s: state, stk: stack)
  ensures exec(append(ii0, ii1), s, stk) == exec(ii1, s, exec(ii0, s, stk))
{
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

type vname = string

datatype aexp = N(n: int) | V(vname) | Plus(aexp, aexp)

type val = int

type state = vname -> val

datatype bexp = Bc(v: bool) | Not(bexp) | And(bexp, bexp) | Less(aexp, aexp)

datatype instr = LOADI(val) | LOAD(vname) | ADD

type stack = List<val>
