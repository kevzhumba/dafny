
// git-issue235.dfy


module A {
  ghost predicate F(x: int)
  {
    true
  }
}

module B {
  lemma Test(x: int)
    ensures I.F(x)
  {
  }

  lemma TestWrapper()
  {
  }

  import I = A
}
