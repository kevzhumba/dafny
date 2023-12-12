
// NameclashesCompile.dfy

method Main()
{
}

datatype Nameclash = Ctor(x: int) {
  method ToString() returns (o: real)
  {
    return 15.0;
  }

  method GetHashCode() returns (o: real)
  {
    return 15.1;
  }
}

codatatype NameclashCo = CoCtor(x: int) {
  const c: int := 94
  const d: int := 99

  function Computer(): real
  {
    0.8
  }

  method Get() returns (u: int)
  {
    return 79;
  }

  method ToString() returns (o: real)
  {
    return 14.3;
  }

  method GetHashCode() returns (o: real)
  {
    return 14.4;
  }
}

newtype NameclashNew = x
  | -18 <= x < 20
{
  method ToString() returns (o: real)
  {
    return 18.9;
  }

  method GetHashCode() returns (o: real)
  {
    return 18.92;
  }
}
