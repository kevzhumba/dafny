
// fun-with-slices.dfy

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[0 .. index]) + s + old(a[index + |s|..])
{
  var i := index;
}
