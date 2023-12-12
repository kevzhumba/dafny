
// Cubes.dfy

method Cubes(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == i * i * i
{
  var n := 0;
  var c := 0;
  var k := 1;
  var m := 6;
}
