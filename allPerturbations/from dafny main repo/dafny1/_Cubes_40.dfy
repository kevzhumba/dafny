
// Cubes.dfy

method Cubes(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == i * i * i
{
}
