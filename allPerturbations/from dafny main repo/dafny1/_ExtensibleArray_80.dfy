
// ExtensibleArray.dfy

method Main()
{
  var a := new ExtensibleArray.Init();
  var n := 0;
  while n < 256 * 256 + 600
    invariant a.Valid() && fresh(a.Repr)
    invariant |a.Contents| == n
  {
    a.Append(n);
    n := n + 1;
  }
  var k := a.Get(570);
  print k, "\n";
  k := a.Get(0);
  print k, "\n";
  k := a.Get(1000);
  print k, "\n";
  a.Set(1000, 23);
  k := a.Get(0);
  print k, "\n";
  k := a.Get(1000);
  print k, "\n";
  k := a.Get(66000);
  print k, "\n";
}

class ExtensibleArray<T> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object?>
  var elements: array?<T>
  var more: ExtensibleArray?<array?<T>>
  var length: int
  var M: int

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    null !in Repr &&
    ((elements == null && more == null && Contents == []) || (elements != null && elements.Length == 256 && elements in Repr)) &&
    (more != null ==>
      more in Repr &&
      more.Repr <= Repr &&
      this !in more.Repr &&
      elements !in more.Repr &&
      more.Valid() &&
      |more.Contents| != 0 &&
      forall j :: 
        0 <= j < |more.Contents| ==>
          more.Contents[j] != null &&
          more.Contents[j].Length == 256 &&
          more.Contents[j] in Repr &&
          more.Contents[j] !in more.Repr &&
          more.Contents[j] != elements &&
          forall k :: 
            0 <= k < |more.Contents| &&
            k != j ==>
              more.Contents[j] != more.Contents[k]) &&
    M == (if more == null then 0 else 256 * |more.Contents|) &&
    0 <= length <= M + 256 &&
    (more != null ==>
      M < length) &&
    length == |Contents| &&
    (forall i :: 
      0 <= i < M ==>
        Contents[i] == more.Contents[i / 256][i % 256]) &&
    forall i :: 
      M <= i < length ==>
        Contents[i] == elements[i - M]
  }

  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == []
  {
    elements := null;
    more := null;
    length := 0;
    M := 0;
    Contents := [];
    Repr := {this};
  }

  method Get(i: int) returns (t: T)
    requires Valid()
    requires 0 <= i < |Contents|
    ensures t == Contents[i]
    decreases Repr
  {
    if M <= i {
      t := elements[i - M];
    } else {
      var arr := more.Get(i / 256);
      t := arr[i % 256];
    }
  }

  method Set(i: int, t: T)
    requires Valid()
    requires 0 <= i < |Contents|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents)[i := t]
  {
    if M <= i {
      elements[i - M] := t;
    } else {
      var arr := more.Get(i / 256);
      arr[i % 256] := t;
    }
    Contents := Contents[i := t];
  }

  method Append(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [t]
    decreases |Contents|
  {
    if elements == null {
      Repr := Repr + {elements};
    }
    if length == 0 || length % 256 != 0 {
      elements[length - M] := t;
    } else {
      if more == null {
        more := new ExtensibleArray.Init();
        Repr := Repr + {more} + more.Repr;
      }
      more.Append(elements);
      Repr := Repr + more.Repr;
      M := M + 256;
      elements := new T[256] (_ /* _v1 */ => t);
      Repr := Repr + {elements};
      elements[0] := t;
    }
    length := length + 1;
    Contents := Contents + [t];
  }
}
