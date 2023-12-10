
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet smallTest/smallFunc.dfy
// smallFunc.dfy

ghost predicate Injective<X(!new), Y>(f: X --> Y)
  requires forall x: X :: f.requires(x)
  reads f.reads
{
  forall x1: X, x2: X :: 
    f(x1) == f(x2) ==>
      x1 == x2
}
