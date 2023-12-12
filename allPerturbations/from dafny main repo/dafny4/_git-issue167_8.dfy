
// git-issue167.dfy

method Main()
{
  LetTest();
  var m := map[6 := 8, 7 := 3];
  var n := Rewrite(m);
  assert m.Keys == n.Keys;
  print n.Keys, "\n";
  var u := {"Alfons", "Milla"};
  var v := Rewrite2(u);
  assert u == v.Keys;
  print v.Keys, "\n";
}

function F(u: int): int
  requires u < 2400
{
  u
}

function G(w: int): int
{
  var g := w + w;
  g - w
}

method LetTest()
{
  var x := var y := "unused"; var y, z := 10, 20; G(F(y)) + z;
  assert x == G(30);
}

function Rewrite(env: map<nat, nat>): map<nat, nat>
{
  var p := map g: nat | g in env :: g;
  map n: nat | n in p :: n
}

function Rewrite_Keys(env: map<nat, nat>): map<nat, nat>
{
  var p := env.Keys;
  map n: nat | n in p :: n
}

function Rewrite2(strs: set<string>): map<string, string>
{
  var p := map g: string | g in strs :: g;
  map s: string | s in p :: s
}

ghost function sum(a: int, b: int): int
{
  a + b
}

ghost predicate sum_is_sum(b: int, c: int)
{
  var s := a => sum(a, b);
  forall a: int :: 
    s(a) + c == a + b + c
}

lemma TestApply(x: int, y: int)
  ensures sum_is_sum(x, y)
{
}

module Test {
  ghost function Convert_AB(f: A): B
  {
    B1
  }

  ghost function Convert_BA(f: B): A
  {
    A1
  }

  ghost function ConvertMap_AB(m: map<A, int>): map<B, int>
  {
    var dom_B := set a | a in m :: Convert_AB(a);
    assert forall u :: u in m.Keys ==> u == A1;
    map b | b in dom_B :: m[Convert_BA(b)]
  }

  datatype A = A1

  datatype B = B1
}
