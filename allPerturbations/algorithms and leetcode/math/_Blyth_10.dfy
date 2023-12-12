
// Blyth.dfy

function powerset<T(==)>(items: set<T>): set<set<T>>
{
  set xs: set<T> | xs <= items
}

method one_one<T(==)>()
{
  var A: set<set<set<set<T>>>> := {{}, {{}}, {{}, {{}}}};
  assert {} <= A;
  assert {} in A;
  assert {{}} in A;
  assert {{}} <= A;
  assert {{{}}} <= A;
  assert {{{}}, {}} <= A;
  var test := {1, 2};
  var pset := powerset(test);
  assert {} <= pset;
  assert {{1}} <= pset;
  assert {{2}} <= pset;
}
