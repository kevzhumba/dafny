
// PrecedenceLinter.dfy

ghost predicate P0(A: bool, B: bool, C: bool)
{
  A &&
  B ==>
    C
}

ghost predicate P1(A: bool, B: bool, C: bool)
{
  A &&
  B ==>
    C
}

ghost predicate P2(A: bool, B: bool, C: bool)
{
  A &&
  B ==>
    C
}

ghost predicate P3(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate P4(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate P5(A: bool, B: bool, C: bool)
{
  A ==>
    B &&
    C
}

ghost predicate P6(A: bool, B: bool, C: bool)
{
  A ==>
    B || C
}

ghost predicate Q0(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q1(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q2(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q3(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q4(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q4a(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q4b(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q4c(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q4d(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q5(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q6(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}

ghost predicate Q7(A: bool, B: bool, C: bool, D: bool)
{
  A ==>
    B &&
    C &&
    D
}

ghost predicate Q8(A: bool, B: bool, C: bool, D: bool)
{
  A ==>
    B &&
    C &&
    D
}

ghost predicate Q8a(A: bool, B: bool, C: bool, D: bool)
{
  (A ==>
    B &&
    C &&
    D) &&
  (B || C)
}

ghost predicate Q8b(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    B &&
    D
}

ghost predicate Q8c(t: int, x: int, y: int)
{
  (t == 2 ==>
    x < y) &&
  (t == 3 || t == 2 ==>
    x == 100 &&
    y == 1000) &&
  (t == 4 ==>
    0 <= x || 0 <= y)
}

ghost predicate Q8d(t: int, x: int, y: int)
{
  t == 3 || t == 2 ==>
    x == 100 &&
    y == 1000
}

ghost predicate Q9(A: bool, B: bool, C: bool)
{
  A ==>
    B ==>
      C
}

ghost predicate R0(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) &&
      R(x)
}

ghost predicate R1(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) &&
    Q(x) ==>
      R(x)
}

ghost predicate R2(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}

ghost predicate R3(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}

ghost predicate R4(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}

ghost predicate R5(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      forall y :: 
        Q(y) ==>
          R(x)
}

ghost predicate R6(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R7(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R8(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R9(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  exists x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}

ghost predicate R10(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  exists x :: 
    P(x) &&
    exists y :: 
      Q(y) &&
      R(x)
}

lemma Injective()
  ensures forall x, y :: Negate(x) == Negate(y) ==> x == y
{
}

ghost function Negate(x: int): int
{
  -x
}

ghost predicate Quant0(s: string)
{
  s != [] &&
  ('a' <= s[0] <= 'z' || 'A' <= s[0] <= 'Z') &&
  forall i :: 
    1 <= i < |s| ==>
      'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z' || '0' <= s[i] <= '9'
}

ghost predicate Quant1(m: array2<string>, P: int -> bool)
  reads m
{
  forall i :: 
    0 <= i < m.Length0 &&
    P(i) ==>
      forall j :: 
        0 <= j < m.Length1 ==>
          m[i, j] != ""
}

ghost predicate Quant2(s: string)
{
  forall i :: 
    0 <= i < |s| ==>
      if s[i] == '*' then false else s[i] == 'a' || s[i] == 'b'
}

ghost predicate Quant3(f: int -> int, g: int -> int)
{
  forall x :: 
    f(x) == g(x)
}

ghost predicate Quant4(f: int -> int, g: int -> int)
{
  forall x :: 
    f(x) == g(x)
}

ghost predicate Quant5(f: int -> int, g: int -> int)
{
  forall x :: 
    f(x) == g(x)
}

ghost function If0(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

ghost function If1(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

ghost function If2(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

ghost function If3(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}

ghost predicate Waterfall(A: bool, B: bool, C: bool, D: bool, E: bool)
{
  A ==>
    B ==>
      C ==>
        D ==>
          E
}

ghost predicate MoreOps0(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) <==
      Q(x) <==
      R(x)
}

ghost predicate MoreOps1(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) <== Q(x) <==> R(x)
}

ghost predicate MoreOps2(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==> Q(x) <==> R(x)
}

ghost predicate MoreOps3(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==> Q(x) <==> R(x) ==> P(x)
}

ghost predicate MoreOps4(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) <==> Q(x) && R(x)
}

lemma IntLemma(x: int)

ghost function StmtExpr0(x: int): int
{
  if x == 17 then
    2
  else
    IntLemma(x); 3
}

ghost function StmtExpr1(x: int): int
{
  if x == 17 then
    2
  else
    IntLemma(x); 3
}

ghost function StmtExpr2(x: int): int
{
  if x == 17 then
    2
  else
    assert x != 17; 3
}

ghost function StmtExpr3(x: int): int
{
  if x == 17 then
    2
  else
    assert x != 17; 3
}

ghost function FunctionWithDefaultParameterValue(x: int, y: int := 100): int

ghost function UseDefaultValues(x: int): int
{
  if x <= 0 then
    0
  else
    FunctionWithDefaultParameterValue(x - 1)
}

ghost function Square(x: int): int
{
  x * x
}

ghost predicate Let0(lo: int, hi: int)
  requires lo <= hi
{
  forall x :: 
    lo <= x < hi ==>
      var square := Square(x); 0 <= square
}

ghost predicate Let1(P: int -> bool)
{
  forall x :: 
    0 <= x &&
    P(x) ==>
      var bigger :| x <= bigger; 0 <= bigger
}

ghost predicate SomeProperty<X>(x: X)

method Parentheses0(arr: array<int>, P: int -> bool)
{
  assert forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i]);
  var x := forall i :: 0 <= i < arr.Length ==> SomeProperty(arr[i]);
  var y := forall i :: 0 <= i < arr.Length ==> P(arr[i]);
  assert forall i :: 0 <= i < arr.Length && SomeProperty(i) ==> unchanged(arr);
  var u := if arr.Length == 3 then true else fresh(arr);
}

method Parentheses1(w: bool, x: int)
{
  var a := if w then {} else {x, x, x};
  var b := if w then iset{} else iset{x, x, x};
  var c := if w then [] else [x, x, x];
  var d := if w then multiset{} else multiset{x, x, x};
  var e := if w then map[] else map[x := x];
  var f := if w then imap[] else imap[x := x];
}

method Parentheses2(w: bool, x: int, y: int)
{
  var a := if w then Record(0, 0) else Record(x, y);
  var b := if w then a else a.(x := y);
}

method Parentheses3(w: bool, arr: array<int>, m: array2<int>, i: nat, j: nat)
  requires i < j < arr.Length <= m.Length0 <= m.Length1
{
  var a := if w then 0 else arr[i];
  var b := if w then [] else arr[i..];
  var c := if w then [] else arr[..i];
  var d := if w then [] else arr[i .. j];
  var e := if w then [] else arr[..j][i..];
  var f := if w then [] else arr[..i] + arr[i..];
  var g := if w then 0 else m[i, j];
  var h := if w then arr[..] else arr[..j][0 := 25];
}

method Parentheses4(w: bool, s: Stream, t: Stream)
{
}

datatype Record = Record(x: int, y: int)

codatatype Stream = More(head: int, tail: Stream)

module MyModule {
  ghost function MyFunction(x: int): int

  lemma Lemma(x: int)
}

module QualifiedNames {
  ghost predicate P(x: int)
  {
    var u := x;
    MyModule.MyFunction(x) == x
  }

  ghost predicate Q(x: int)
  {
    var u := x;
    MyModule.Lemma(x);
    x == MyModule.MyFunction(x)
  }

  ghost function F(): int
  {
    var p := 1000;
    MyModule.Lemma(p);
    p
  }

  ghost predicate R(x: int)
  {
    var u := x;
    MyModule.Lemma(x);
    x == MyModule.MyFunction(x)
  }

  import MyModule
}

module MatchAcrossMultipleLines {
  method M(s: set<PQ>)
    requires forall pq | pq in s :: match pq { case P(x) => true case Q(y) => y == false }
  {
  }

  ghost function F(A: bool, B: int, C: YZ): int
    requires C != Y
  {
    if A then
      B
    else
      match C { case Z => 3 }
  }

  datatype PQ = P(int) | Q(bool)

  datatype YZ = Y | Z
}
