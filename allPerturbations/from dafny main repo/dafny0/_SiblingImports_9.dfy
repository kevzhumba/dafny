
// SiblingImports.dfy

method Main()
{
  ClientB.Test();
  ClientC.Test();
  ClientD.Test();
  ClientE.Test();
  ClientF.Test();
  ClientG.Test();
  Kevin.Test();
}

module Library {
  function Max(x: int, y: int): int
  {
    if x < y then
      y
    else
      x
  }

  function More(x: int): int
  {
    x + 2
  }

  function Less(x: int): int
  {
    x - 2
  }

  export
    reveals Max


  export X
    reveals More


  export Y
    reveals Less


  export Z extends Library, X

}

module ClientA {
  method Test()
  {
    print "ClientA.Inner.Five: ", Inner.Five(), "\n";
  }

  import Library

  module Inner {
    function Five(): int
    {
      Library.Max(2, 5)
    }

    import Library
  }
}

module ClientB {
  method Test()
  {
    print "ClientB.Inner.Five: ", Inner.Five(), "\n";
  }

  import Library

  module Inner {
    function Five(): int
    {
      L.Max(2, 5)
    }

    import L = Library
  }
}

module ClientC {
  method Test()
  {
    print "ClientC.Inner.Five: ", Inner.Five(), "\n";
  }

  import L = Library

  module Inner {
    function Five(): int
    {
      K.Max(2, 5)
    }

    import K = Library
  }
}

module ClientD {
  method Test()
  {
    print "ClientD.Inner.Five: ", Inner.Five(), "\n";
  }

  import L = Library`X

  module Inner {
    function Five(): int
    {
      K.Less(7)
    }

    import K = Library`Y
  }
}

module ClientE {
  method Test()
  {
    print "ClientE.Inner.Five: ", Inner.Five(), "\n";
  }

  import L = Library`Z

  module Inner {
    function Five(): int
    {
      K.Max(2, 5)
    }

    import K = Library
  }
}

module ClientF {
  method Test()
  {
    print "ClientF.Inner.Five: ", Inner.Five(), "\n";
  }

  import opened L = Library`Z

  module Inner {
    function Five(): int
    {
      K.Max(2, 5)
    }

    import K = Library
  }
}

module ClientG {
  method Test()
  {
    print "ClientG.Inner.Five: ", Inner.Five(), "\n";
  }

  import Library

  module Inner {
    function Five(): int
    {
      Max(2, 5)
    }

    import opened K = Library
  }
}

module Kevin {
  method Test()
  {
    print "Frankie: ", Joe.Nick.g(), "\n";
  }

  module Joe {

    module Nick {
      function g(): int
      {
        Frankie.x
      }

      import Frankie
    }
  }
}

module Frankie {
  const x := 3
}
