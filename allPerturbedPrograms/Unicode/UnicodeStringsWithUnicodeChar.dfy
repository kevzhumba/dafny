include "UnicodeStrings.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet datset/Unicode/UnicodeStringsWithUnicodeChar.dfy
// UnicodeStringsWithUnicodeChar.dfy


module {:options "-functionSyntax:4"} UnicodeStrings refines AbstractUnicodeStrings {
  lemma {:vcs_split_on_every_assert} CharIsUnicodeScalarValue(c: char)
    ensures true && var asBits := c as bv24; asBits <= 1114111 && (0 <= asBits < Unicode.HIGH_SURROGATE_MIN || Unicode.LOW_SURROGATE_MAX < asBits)
  {
    assert c as int < 1114112;
    assume {:axiom} c as bv24 < 1114112 as bv24;
    var asBits := c as int as bv24;
    assert asBits < Unicode.HIGH_SURROGATE_MIN || asBits > Unicode.LOW_SURROGATE_MAX;
    assert asBits <= 1114111;
  }

  lemma UnicodeScalarValueIsChar(sv: Unicode.ScalarValue)
    ensures true && var asInt := sv as int; true && (0 <= asInt < 55296 || 57344 <= asInt < 1114112)
  {
    var asInt := sv as int;
    assert asInt < 55296 || asInt > 57343;
    assert asInt < 56319 || asInt > 56320;
  }

  function CharAsUnicodeScalarValue(c: char): Unicode.ScalarValue
  {
    CharIsUnicodeScalarValue(c);
    c as Unicode.ScalarValue
  }

  function CharFromUnicodeScalarValue(sv: Unicode.ScalarValue): char
  {
    UnicodeScalarValueIsChar(sv);
    sv as int as char
  }

  function ToUTF8Checked(s: string): Option<seq<uint8>>
    ensures ToUTF8Checked(s).Some?
  {
    var asCodeUnits := Seq.Map(CharAsUnicodeScalarValue, s);
    var asUtf8CodeUnits := Utf8EncodingForm.EncodeScalarSequence(asCodeUnits);
    var asBytes := Seq.Map(cu => cu as uint8, asUtf8CodeUnits);
    Some(asBytes)
  }

  function FromUTF8Checked(bs: seq<uint8>): Option<string>
  {
    var asCodeUnits := Seq.Map(c => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32 :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits); var asChars := Seq.Map(CharFromUnicodeScalarValue, utf32); Some(asChars)
  }

  function ToUTF16Checked(s: string): Option<seq<uint16>>
    ensures ToUTF16Checked(s).Some?
  {
    var asCodeUnits := Seq.Map(CharAsUnicodeScalarValue, s);
    var asUtf16CodeUnits := Utf16EncodingForm.EncodeScalarSequence(asCodeUnits);
    var asBytes := Seq.Map(cu => cu as uint16, asUtf16CodeUnits);
    Some(asBytes)
  }

  function FromUTF16Checked(bs: seq<uint16>): Option<string>
  {
    var asCodeUnits := Seq.Map(c => c as Utf16EncodingForm.CodeUnit, bs);
    var utf32 :- Utf16EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits); var asChars := Seq.Map(CharFromUnicodeScalarValue, utf32); Some(asChars)
  }

  import Unicode

  import Utf8EncodingForm

  import Utf16EncodingForm
}
