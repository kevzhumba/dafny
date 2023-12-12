
// Constant.dfy

const one: int := 1
const two: int := one * 2
const three: int := one + two
const Pi: real := 3.14

method Main()
{
  print "one := ", one, "\n";
  print "two := ", two, "\n";
  print "three := ", three, "\n";
  assert three == 3;
  assert Pi == 3.14;
  var weeks := Calendar.weeks;
  print "months := ", Calendar.months, "\n";
  print "weeks := ", weeks, "\n";
  assert weeks == 52;
  var c := new C;
  var tu := c.M();
  print tu, " ";
  print c.G(c), " ";
  print c.H(c), " ";
  print C.x, " ";
  var g := new Generic<real>;
  var putItHere := g.y;
  print putItHere, " ";
  var go := g.M();
  print go, "\n";
  var noRhs := new NoRHS;
  print "noRhs.y = ", noRhs.y, "\n";
  var cl := new Class;
  cl.Test();
  var ii := new InstanceInit(13);
  print ii.x0, " ", ii.x1, " ", ii.y2, " ", ii.y3, " ", ii.r, "\n";
  print mmgg, " ", UninterpretedStaticsTrait.mmtt, " ", UninterpretedStaticsClass.mmcc, "\n";
  InitializationDependencies.PrintEm();
}

method MMethod(tr: Trait?)
{
  assert Trait.y == 7;
  assert tr.y == 7;
  assert tr == null || tr.x1 == 7;
}

const mmgg: Six

class Calendar {
  static const months: int := 12
  static const weeks: int := 52
}

class C {
  static const x: int := y + 1
  static const y: int := 5
  var z: int

  static function G(c: C): int
    ensures G(c) == 16
  {
    x + y + c.y
  }

  const a: int := b + 2
  const b: int := 50

  function H(c: C): int
    ensures H(c) == 50 + 52 + 50 + 6 + 5 + 5 + 5 == 173
  {
    a + b + c.b + x + y + c.y + C.y
  }

  method M() returns (r: int)
    ensures r == 11
  {
    r := x + y;
  }
}

class Generic<G> {
  const y: int := 63

  method M() returns (q: int)
    ensures q == 63
  {
    q := this.y;
  }
}

newtype Six = x
  | 6 <= x
  witness 6

class NoRHS {
  const y: Six
}

trait Trait {
  const x0: Six
  const x1: Six := 7
  static const y: Six := 7
}

class Class extends Trait {
  method Test()
  {
    assert x1 == 7 && y == 7;
    print x0, " ", x1, " ", y, "\n";
  }
}

class InstanceInit extends Trait {
  const y2: Six
  const y3: Six := 12
  const N: int := 20
  var r: real

  constructor (u: Six)
    requires 10 <= u
  {
    x0 := 80 + u;
    var arr := new real[N];
    arr[8] := 2.7;
    r := arr[8];
    y2 := 77 + y3;
    new;
    assert x0 == u + 80 && x1 == 7;
    assert y2 == 89 && y3 == 12;
    assert arr.Length == 20;
    arr[9] := 3.14;
    r := r + arr[8] + arr[9];
  }
}

trait UninterpretedStaticsTrait {
  static const mmtt: Six
}

class UninterpretedStaticsClass extends UninterpretedStaticsTrait {
  static const mmcc: Six
}

type byte = x
  | 0 <= x < 256

class MyClass {
  const B: array<byte>

  method M()
  {
    var x: array?<byte> := B;
    var y: array<byte> := x;
  }
}

class MyOnePurposeClass {
  static const z: int
  static const w: int := 76
  static const self: MyOnePurposeClass?
}

class MyGenericClass<X(00), Y(00)> {
  static ghost const x: X
  static ghost const y: Y
  static const z: int
  static const w: int := 76
  static const self: MyGenericClass?<X, Y>
  static const almostSelf: MyGenericClass?<Y, X>
  static const another: MyGenericClass?<byte, seq<X>>
}

module InitializationDependencies {
  method PrintEm()
  {
    print C.a, " ";
    print C.b, " ";
    print C.c, "\n";
    print D.m, "\n";
    var r := new R;
    print r.a, " ";
    print r.b, " ";
    print r.c, " ";
    print r.m, "\n";
    print r.n, "\n";
  }

  class C {
    static const a: int := b
    static const b: int := D.m
    static const c: int := b
  }

  class D {
    static const m: int := 20
  }

  class R {
    const a: int := b + b
    const b: int := this.m
    const c: int := b
    const m: int := 21
    const n: int := F(b)

    function F(nn: int): int
    {
      2 * nn + C.b
    }
  }
}

module A {
  const x: int := 100
}

module B refines A {
  ghost const x: int

  lemma TestRhsIsInherited()
  {
    assert x == 100;
  }
}
