
// BoatsToSavePeople.dfy

function sumBoat(s: seq<nat>): nat
  requires 1 <= |s| <= 2
{
  if |s| == 1 then
    s[0]
  else
    s[0] + s[1]
}

predicate isSafeBoat(boat: seq<nat>, limit: nat)
{
  1 <= |boat| <= 2 &&
  sumBoat(boat) <= limit
}

function multisetAdd(ss: seq<seq<nat>>): multiset<nat>
{
  if ss == [] then
    multiset{}
  else
    multiset(ss[0]) + multisetAdd(ss[1..])
}

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>)
{
  multiset(xs) == multisetAdd(ss)
}

predicate allSafe(boats: seq<seq<nat>>, limit: nat)
{
  forall boat :: 
    boat in boats ==>
      isSafeBoat(boat, limit)
}

predicate sorted(list: seq<int>)
{
  forall i, j :: 
    0 <= i < j < |list| ==>
      list[i] <= list[j]
}

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
  requires |people| >= 1
  requires sorted(people)
  requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
  ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{
  boats := 0;
  var lower: nat := 0;
  var upper: int := |people| - 1;
  ghost var visitedUpper: multiset<nat> := multiset{};
  ghost var visitedLower: multiset<nat> := multiset{};
  ghost var remaining: multiset<nat> := multiset(people);
  ghost var safeBoats: seq<seq<nat>> := [];
  while lower <= upper
    invariant 0 <= lower <= |people|
    invariant lower - 1 <= upper < |people|
    invariant visitedUpper == multiset(people[upper + 1..])
    invariant visitedLower == multiset(people[..lower])
    invariant allSafe(safeBoats, limit)
    invariant multisetAdd(safeBoats) == visitedLower + visitedUpper
    invariant |safeBoats| == boats
  {
    if people[upper] == limit || people[upper] + people[lower] > limit {
      boats := boats + 1;
      assert isSafeBoat([people[upper]], limit);
      safeBoats := [[people[upper]]] + safeBoats;
      assert visitedUpper == multiset(people[upper + 1..]);
      ghost var gu := people[upper + 1..];
      assert multiset(gu) == visitedUpper;
      assert people[upper..] == [people[upper]] + gu;
      visitedUpper := visitedUpper + multiset{people[upper]};
      upper := upper - 1;
      assert people[upper + 1..] == [people[upper + 1]] + gu;
    } else {
      ghost var gl := people[..lower];
      boats := boats + 1;
      if lower == upper {
        visitedLower := visitedLower + multiset{people[lower]};
        assert isSafeBoat([people[lower]], limit);
        safeBoats := [[people[lower]]] + safeBoats;
      } else {
        ghost var gu := people[upper + 1..];
        assert multiset(gu) == visitedUpper;
        visitedUpper := visitedUpper + multiset{people[upper]};
        visitedLower := visitedLower + multiset{people[lower]};
        assert isSafeBoat([people[upper], people[lower]], limit);
        safeBoats := [[people[upper], people[lower]]] + safeBoats;
        upper := upper - 1;
        assert people[upper + 1..] == [people[upper + 1]] + gu;
      }
      lower := lower + 1;
      assert people[..lower] == gl + [people[lower - 1]];
    }
  }
  assert visitedLower == multiset(people[..lower]);
  assert visitedUpper == multiset(people[upper + 1..]);
  assert people == people[..lower] + people[upper + 1..];
  assert visitedLower + visitedUpper == multiset(people);
}
