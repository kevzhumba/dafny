
// ParserOptions.dfy

method Main()
{
}

module {:options "/functionSyntax:3"} FunctionMethodSyntax {
  function CompiledFunction(): int
  {
    1
  }

  ghost function GhostFunction(): int
  {
    1
  }
}

module {:options "/functionSyntax:4"} GhostFunctionSyntax {
  function CompiledFunction(): int
  {
    1
  }

  ghost function GhostFunction(): int
  {
    1
  }
}

module {:options "/functionSyntax:3"} {:options "/functionSyntax:4"} StillGhostFunctionSyntax {
  function CompiledFunction(): int
  {
    1
  }

  ghost function GhostFunction(): int
  {
    1
  }
}

module BackToDefault {
  function CompiledFunction(): int
  {
    1
  }

  ghost function GhostFunction(): int
  {
    1
  }
}
