
// ForallCompilationNewSyntax.dfy

method Main()
{
  var c := new MyClass;
  c.arr := new int[10, 20];
  c.K0(3, 12);
  c.K1(3, 12);
  c.K2(3, 12);
  c.K3(3, 12);
  c.K4(12);
  c.M();
  c.N();
  c.P();
  c.Q();
}

class MyClass {
  var arr: array2<int>

  method K0(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    forall k | k in {-3, 4} {
      arr[i, j] := 50;
    }
  }

  method K1(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
  {
    forall k | k in {} {
      arr[i, j] := k;
    }
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    forall k | k in {-3, 4} {
    }
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    forall i, k: nat | 0 <= i < arr.Length0 && k in {-3, 4} {
      arr[i, j] := k;
    }
  }

  method M()
  {
    var ar := new int[3, 3];
    var S: set<int> := {2, 0};
    forall k | k in S {
      ar[k, 1] := 0;
    }
    forall k, j | k in S && j in S {
      ar[k, j] := 0;
    }
  }

  method N()
  {
    var ar := new int[3, 3];
    ar[2, 2] := 0;
  }

  method P()
  {
    var ar := new int[3];
    var prev := ar[..];
    var S: set<int> := {};
    forall k | k in S {
      ar[k] := 0;
    }
    assert ar[..] == prev;
  }

  method Q()
  {
    var ar := new int[3, 3];
    var S: set<int> := {1, 2};
    forall k | k in S {
      ar[0, 0] := 0;
    }
    assert ar[0, 0] == 0;
  }
}
