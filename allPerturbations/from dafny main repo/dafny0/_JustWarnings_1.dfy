
// JustWarnings.dfy

method M(x: int)
{
  var x := 9;
}

class C<T> {
  var u: T

  method P<T>(t: T)

  constructor (t: T)
  {
    u := t;
  }
}
