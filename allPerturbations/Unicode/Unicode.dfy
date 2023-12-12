include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet datset/Unicode/Unicode.dfy
// Unicode.dfy


module {:options "-functionSyntax:4"} Unicode {
  const HIGH_SURROGATE_MIN: CodePoint := 55296
  const HIGH_SURROGATE_MAX: CodePoint := 56319
  const LOW_SURROGATE_MIN: CodePoint := 56320
  const LOW_SURROGATE_MAX: CodePoint := 57343
  const ASSIGNED_PLANES: set<bv8> := {0, 1, 2, 3, 14, 15, 16}

  ghost predicate {:opaque} IsInAssignedPlane(i: CodePoint)
  {
    var plane := (i >> 16) as bv8;
    plane in ASSIGNED_PLANES
  }

  import opened Wrappers

  import Seq

  type CodePoint = i: bv24
    | 0 <= i <= 1114111

  type HighSurrogateCodePoint = p: CodePoint
    | HIGH_SURROGATE_MIN <= p <= HIGH_SURROGATE_MAX
    witness HIGH_SURROGATE_MIN

  type LowSurrogateCodePoint = p: CodePoint
    | LOW_SURROGATE_MIN <= p <= LOW_SURROGATE_MAX
    witness LOW_SURROGATE_MIN

  type ScalarValue = p: CodePoint
    | (p < HIGH_SURROGATE_MIN || p > HIGH_SURROGATE_MAX) && (p < LOW_SURROGATE_MIN || p > LOW_SURROGATE_MAX)

  type AssignedCodePoint = p: CodePoint
    | IsInAssignedPlane(p)
    witness *
}
