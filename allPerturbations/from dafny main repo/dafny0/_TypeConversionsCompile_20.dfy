
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
