
// TypeConversionsCompile.dfy

method Print(x: int, n: nat, r: real, handful: Handful, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
{
  print x, " ", n, " ", r, " ", handful, " ", even, " ", small, " ", b67, " ", w, " ", seven, " ", noll, "\n";
}

method PrintExpected<T>(got: T, expected: T)
{
  print "got ", got, ", expected ", expected, "\n";
}

method Main()
{
  var x: int, n: nat, r: real := 3, 4, 5.0;
  var handful: Handful, even: EvenInt, small: SmallReal := 5, 6, -1.0;
  var b67: bv67, w: bv32, seven: bv7, noll: bv0 := 147573952589676412927, 4294967295, 127, 0;
  Print(x, n, r, handful, even, small, b67, w, seven, noll);
  PrintExpected(x as bv7, 3);
  PrintExpected(0 as bv0, 0);
  PrintExpected(r as int, 5);
  PrintExpected((2.0 * r) as EvenInt, 10);
  PrintExpected(x as real, 3.0);
  PrintExpected(even as real, 6.0);
  PrintExpected((small + 3.0) as Handful, 2);
  PrintExpected(noll as Handful, 0);
  PrintExpected(noll as SmallReal, 0.0);
  PrintExpected(w as real, 4294967295.0);
  PrintExpected(seven as real, 127.0);
  PrintExpected(noll as bv32, 0);
  PrintExpected(noll as bv67, 0);
  PrintExpected(seven as bv32, 127);
  PrintExpected(seven as bv67, 127);
  b67 := 50;
  PrintExpected(r as bv67, 5);
  PrintExpected(r as bv32, 5);
  PrintExpected(w as bv67, 4294967295);
  PrintExpected(r as bv7, 5);
  PrintExpected(0.0 as bv0, 0);
  PrintExpected(handful as bv67, 5);
  PrintExpected(handful as bv32, 5);
  PrintExpected(handful as bv7, 5);
  PrintExpected(handful as int, 5);
  PrintExpected(noll as bv32 as bv0, 0);
  PrintExpected(noll as bv67 as bv0, 0);
  PrintExpected(seven as bv32 as bv7, 127);
  PrintExpected(seven as bv67 as bv7, 127);
  PrintExpected(handful as real, 5.0);
  Difficult();
  var a0: Abundance, a1: Abundance, a2: Abundance, lng: int64;
  var s := {4.0, 6.3, r, 1000.2};
  var a := new char[68];
  handful := 120 as Handful;
  a0, a1 := -1 as Abundance, 4 as Abundance;
  a2 := 8589934592 as Abundance;
  w, lng := 6345789 as bv32, -9223372036854775808 as int64;
  print handful, " ", a0, " ", a1, " ", a2, " ", w, " ", lng, "\n";
  x, handful, a0, w := |s|, |s| as Handful, |s| as Abundance, |s| as bv32;
  print x, " ", handful, " ", a0, " ", w, "\n";
  x, handful, a0, w := a.Length, a.Length as Handful, a.Length as Abundance, a.Length as bv32;
  print x, " ", handful, " ", a0, " ", w, "\n";
}

method Difficult()
{
  if 14 as real as int as bv67 == 14 {
    PrintExpected(14 as real as int as bv67 as EvenInt as SmallReal as Handful as bv7 as bv32 as int, 14);
  }
}

method OrdinalTests()
{
  var ord: ORDINAL := 143;
  var iord := ord as int;
  var oord := iord as ORDINAL;
  print "Something about ORDINAL: ", ord, " ", iord, " ", oord, " ", ord + 4, " ", ord - 100, "\n";
  print "ORDINAL and bitvectors: ", 20 as bv32 as ORDINAL, " ", 20 as bv300 as ORDINAL, "\n";
  print ord.IsLimit, " ", ord.Offset, " ", ord.IsNat, "\n";
  ord := 0;
  print ord.IsLimit, " ", ord.Offset, " ", ord.IsNat, "\n";
}

newtype Handful = x
  | 0 <= x < 32768

newtype Abundance = y
  | -20 <= y < 2199023255552

newtype int64 = y
  | -9223372036854775808 <= y < 9223372036854775808

newtype EvenInt = x
  | x % 2 == 0

newtype SmallReal = r
  | -4.0 <= r < 300.0
