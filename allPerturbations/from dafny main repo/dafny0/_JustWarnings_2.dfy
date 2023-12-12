
// JustWarnings.dfy

method M(x: int)
{
}

class C<T> {
  var u: T

  method P<T>(t: T)

  constructor (t: T)
  {
    u := t;
  }
}
