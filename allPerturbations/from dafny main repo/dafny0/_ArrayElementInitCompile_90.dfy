
// ArrayElementInitCompile.dfy

method Main()
{
  var a := SingleValued(67);
  PrintArray(a);
  var mx := NewMatrix();
  PrintMatrix(mx);
  var c := InitArray(F);
  PrintArray(c);
  var s := InitArray(_ /* _v0 */ => 12);
  PrintArray(s);
  var t := new TrickyLets(0, null);
  t.RegressionTests();
  t.Do();
  t.DoDisplay();
  t.DoDefault();
  SubsetType();
  Display(98);
}

method SingleValued(d: int) returns (a: array<int>)
  ensures a.Length == 8
{
  a := new int[8] (_ /* _v1 */ => d);
}

function F(x: int): char
{
  if x % 2 == 0 then
    'O'
  else
    '.'
}

method InitArray<D>(f: int -> D) returns (a: array<D>)
  requires forall x :: 0 <= x < 12 ==> f.requires(x)
{
  a := new D[12] (f);
}

method NewMatrix() returns (m: array2<int>)
{
  m := new int[5, 4] ((x, y) => x + y);
}

method PrintMatrix(m: array2<int>)
{
  var i := 0;
  while i < m.Length0 {
    var j := 0;
    while j < m.Length1 {
      print m[i, j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
}

method PrintArray<D>(a: array<D>)
{
  var i := 0;
  while i < a.Length {
    print a[i], " ";
    i := i + 1;
  }
  print "\n";
}

method SubsetType()
{
  var a := new Six[12];
  assert 6 <= a[6];
  print a[6], "\n";
}

method Display(n: nat)
{
  var b := new nat[4] [100, 75, n, 25];
  var d := new char[0] [];
  var s := new string[4] ["looks", "like", "this", "rocks"];
  var i := new int32[7] [-2, -1, 0, 1, 2, 3, 4];
  PrintArray(b);
  PrintArray(d);
  PrintArray(s);
  PrintArray(i);
}

class TrickyLets {
  var next: TrickyLets?
  var arr: array<char>

  constructor (n: nat, w: TLWrapper?)
    modifies w
    ensures w != null ==> w.data == null
  {
    if w != null {
      w.data := null;
    }
    if n != 0 {
      next := new TrickyLets(n - 1, null);
    }
  }

  method RegressionTests()
  {
    var t := new TrickyLets(0, null);
    var w := new TLWrapper;
    w.data := t;
    w.data, w.data.next := null, null;
    t := new TrickyLets(0, null);
    w := new TLWrapper;
    w.data := t;
    w.data.next, w.data := null, null;
    w := new TLWrapper;
    w.data := t;
    w.data.next := new TrickyLets(0, w);
    assert t.next != null;
    assert w.data == null;
  }

  method Do()
    modifies this
  {
    this.arr := new char[20] (_ /* _v2 */ => 'D');
    assert arr[12] == 'D';
    print arr[12], " ";
    (var u := this; u).arr := new char[var n := 20; n] (var fn := _ /* _v3 */ => 'E'; fn);
    assert arr[13] == 'E';
    print arr[13], "\n";
  }

  method DoDisplay()
    modifies this
  {
    this.arr := new char[3] ['x', 'y', 'z'];
    assert arr[1] == 'y';
    print arr[1], " ";
    (var u := this; u).arr := new char[var n := 3; n] [var x := 'x'; x, var y := 'y'; y, var z := 'z'; z];
    assert arr[2] == 'z';
    print arr[2], "\n";
  }

  method DoDefault()
    modifies this
  {
    this.arr := new char[4];
    assert arr.Length == 4;
    print arr.Length, " ";
    (var u := this; u).arr := new char[var n := 3; n];
    assert arr.Length == 3;
    print arr.Length, "\n";
  }
}

class TLWrapper {
  var data: TrickyLets?
}

type Six = x
  | 6 <= x
  witness 7

newtype int32 = x
  | -2147483648 <= x < 2147483648
