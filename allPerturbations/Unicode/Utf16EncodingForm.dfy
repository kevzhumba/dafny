include "../Collections/Sequences/Seq.dfy"
include "../Functions.dfy"
include "Unicode.dfy"
include "UnicodeEncodingForm.dfy"
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet datset/Unicode/Utf16EncodingForm.dfy
// Utf16EncodingForm.dfy


module {:options "-functionSyntax:4"} Utf16EncodingForm refines UnicodeEncodingForm {
  function IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
  {
    if |s| == 1 then
      IsWellFormedSingleCodeUnitSequence(s)
    else if |s| == 2 then
      var b := IsWellFormedDoubleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else
      false
  }

  function IsWellFormedSingleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 1
  {
    var firstWord := s[0];
    0 <= firstWord <= 55295 || 57344 <= firstWord <= 65535
  }

  function IsWellFormedDoubleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 2
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1])
  {
    var firstWord := s[0];
    var secondWord := s[1];
    55296 <= firstWord <= 56319 &&
    56320 <= secondWord <= 57343
  }

  function SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==> true && maybePrefix.Some?
    ensures maybePrefix.Some? ==> true && var prefix := maybePrefix.Extract(); 0 < |prefix| <= |s| && prefix == s[..|prefix|] && IsMinimalWellFormedCodeUnitSubsequence(prefix)
  {
    if |s| >= 1 && IsWellFormedSingleCodeUnitSequence(s[..1]) then
      Some(s[..1])
    else if |s| >= 2 && IsWellFormedDoubleCodeUnitSequence(s[..2]) then
      Some(s[..2])
    else
      None
  }

  function EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
  {
    if 0 <= v <= 55295 || 57344 <= v <= 65535 then
      EncodeScalarValueSingleWord(v)
    else
      EncodeScalarValueDoubleWord(v)
  }

  function EncodeScalarValueSingleWord(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 0 <= v <= 55295 || 57344 <= v <= 65535
    ensures |m| == 1
    ensures IsWellFormedSingleCodeUnitSequence(m)
  {
    var firstWord := v as CodeUnit;
    [firstWord]
  }

  function EncodeScalarValueDoubleWord(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 65536 <= v <= 1114111
    ensures |m| == 2
    ensures IsWellFormedDoubleCodeUnitSequence(m)
  {
    var x2 := (v & 1023) as bv10;
    var x1 := (v & 64512 >> 10) as bv6;
    var u := (v & 2031616 >> 16) as bv5;
    var w := (u - 1) as bv4;
    var firstWord := 55296 | (w as CodeUnit << 6) | x1 as CodeUnit;
    var secondWord := 56320 | x2 as CodeUnit;
    [firstWord, secondWord]
  }

  function DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
  {
    if |m| == 1 then
      DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
    else
      assert |m| == 2; DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)
  }

  function DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 1
    ensures 0 <= v <= 55295 || 57344 <= v <= 65535
    ensures EncodeScalarValueSingleWord(v) == m
  {
    var firstWord := m[0];
    var x := firstWord as bv16;
    assert EncodeScalarValueSingleWord(x as Unicode.ScalarValue) == m;
    x as Unicode.ScalarValue
  }

  function DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 2
    ensures 65536 <= v <= 1114111
    ensures EncodeScalarValueDoubleWord(v) == m
  {
    var firstWord := m[0];
    var secondWord := m[1];
    var x2 := (secondWord & 1023) as bv24;
    var x1 := (firstWord & 63) as bv24;
    var w := (firstWord & 960 >> 6) as bv24;
    var u := (w + 1) as bv24;
    var v := (u << 16) | (x1 << 10) | x2 as Unicode.ScalarValue;
    assert {:split_here} true;
    assert EncodeScalarValueDoubleWord(v) == m;
    v
  }

  type CodeUnit = bv16
}
