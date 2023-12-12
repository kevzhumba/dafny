include "../Collections/Sequences/Seq.dfy"
include "../BoundedInts.dfy"
include "Unicode.dfy"
include "Utf8EncodingForm.dfy"
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet datset/Unicode/Utf8EncodingScheme.dfy
// Utf8EncodingScheme.dfy


module {:options "-functionSyntax:4"} Utf8EncodingScheme {
  function Serialize(s: Utf8EncodingForm.CodeUnitSeq): (b: seq<byte>)
  {
    Seq.Map(c => c as byte, s)
  }

  function Deserialize(b: seq<byte>): (s: Utf8EncodingForm.CodeUnitSeq)
  {
    Seq.Map(b => b as Utf8EncodingForm.CodeUnit, b)
  }

  lemma LemmaSerializeDeserialize(s: Utf8EncodingForm.CodeUnitSeq)
    ensures Deserialize(Serialize(s)) == s
  {
  }

  lemma LemmaDeserializeSerialize(b: seq<byte>)
    ensures Serialize(Deserialize(b)) == b
  {
    calc {
      Serialize(Deserialize(b));
    ==
      Seq.Map(c => c as byte, Seq.Map(b => b as Utf8EncodingForm.CodeUnit, b));
    ==
      Seq.Map(b => b as Utf8EncodingForm.CodeUnit as byte, b);
    ==
      Seq.Map(b => b, b);
    ==
      b;
    }
  }

  import opened Wrappers

  import BoundedInts

  import Seq

  import Unicode

  import Utf8EncodingForm

  type byte = BoundedInts.uint8
}
