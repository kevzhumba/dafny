
// git-issue4.dfy

function IntToChar(i: int): char
  requires 0 <= i < 10
{
  (48 + i) as char
}

function CharToInt(i: char): int
{
  i as int - 48
}

method Main()
{
  print IntToChar(8), "\n";
  print CharToInt('8'), "\n";
  Regression();
}

method Regression()
{
}

type mySubtype = x: int
  | 0 <= x < 100000

newtype myNative = x: int
  | 0 <= x < 100000
