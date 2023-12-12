
// ModuleInsertion.dfy

method Main()
{
}

module Outer {
  method Test()
  {
    print A.a, " ", B.b, " ", C.c, " ", D.d, "\n";
  }

  module C {
    const c := 2 + D.d

    import D
  }

  module A {
    const a := B.b + C.c

    import B

    import C
  }

  module B {
    const b := 1
  }

  module D {
    const d := 3
  }

  module E {

    export
      provides F


    module F {

      export G

    }
  }

  module H {

    import E

    import F = E.F`G
  }
}

module XY {
  method Test()
  {
    print X.m, " ", X.M.n, " ", Y.m, "\n";
  }

  module X {
    const m := 20

    module M {
      const n := Y.m - 5

      import Y
    }
  }

  module Y {
    const m := 22
  }
}

module MyModule {

  module Q {

    module W {

      module E {

        module R {

          module T {

            module Y {
              const h := 2
            }
          }
        }
      }
    }
  }
}

module U {

  module V {
    const x2 := 14 + W.x1 + W.X.x0

    method Test()
    {
      print W.X.x0, " ", W.x1, " ", x2, "\n";
    }

    module W {
      const x1 := 12 * X.x0

      module X {
        const x0 := 12
      }
    }
  }
}
