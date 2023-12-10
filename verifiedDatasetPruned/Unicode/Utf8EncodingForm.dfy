include "../Collections/Sequences/Seq.dfy"
include "../Functions.dfy"
include "Unicode.dfy"
include "UnicodeEncodingForm.dfy"
// dafny 4.3.0.0
// Command Line Options: /compile:0 /perturb /quiet datset/Unicode/Utf8EncodingForm.dfy
// Utf8EncodingForm.dfy


module {:options "-functionSyntax:4"} Utf8EncodingForm refines UnicodeEncodingForm {
  function IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
  {
    if |s| == 1 then
      var b := IsWellFormedSingleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else if |s| == 2 then
      var b := IsWellFormedDoubleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else if |s| == 3 then
      var b := IsWellFormedTripleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else if |s| == 4 then
      var b := IsWellFormedQuadrupleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else
      false
  }

  function IsWellFormedSingleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 1
  {
    var firstByte := s[0];
    true &&
    0 <= firstByte <= 127
  }

  function IsWellFormedDoubleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 2
    ensures b ==> true && !IsWellFormedSingleCodeUnitSequence(s[..1])
  {
    var firstByte := s[0];
    var secondByte := s[1];
    194 <= firstByte <= 223 &&
    128 <= secondByte <= 191
  }

  function IsWellFormedTripleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 3
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1]) && !IsWellFormedDoubleCodeUnitSequence(s[..2])
  {
    var firstByte := s[0];
    var secondByte := s[1];
    var thirdByte := s[2];
    ((firstByte == 224 && 160 <= secondByte <= 191) || (225 <= firstByte <= 236 && 128 <= secondByte <= 191) || (firstByte == 237 && 128 <= secondByte <= 159) || (238 <= firstByte <= 239 && 128 <= secondByte <= 191)) &&
    128 <= thirdByte <= 191
  }

  function IsWellFormedQuadrupleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 4
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1]) && !IsWellFormedDoubleCodeUnitSequence(s[..2]) && !IsWellFormedTripleCodeUnitSequence(s[..3])
  {
    var firstByte := s[0];
    var secondByte := s[1];
    var thirdByte := s[2];
    var fourthByte := s[3];
    ((firstByte == 240 && 144 <= secondByte <= 191) || (241 <= firstByte <= 243 && 128 <= secondByte <= 191) || (firstByte == 244 && 128 <= secondByte <= 143)) &&
    128 <= thirdByte <= 191 &&
    128 <= fourthByte <= 191
  }

  function SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
  {
    if |s| >= 1 && IsWellFormedSingleCodeUnitSequence(s[..1]) then
      Some(s[..1])
    else if |s| >= 2 && IsWellFormedDoubleCodeUnitSequence(s[..2]) then
      Some(s[..2])
    else if |s| >= 3 && IsWellFormedTripleCodeUnitSequence(s[..3]) then
      Some(s[..3])
    else if |s| >= 4 && IsWellFormedQuadrupleCodeUnitSequence(s[..4]) then
      Some(s[..4])
    else
      None
  }

  function EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
  {
    if v <= 127 then
      EncodeScalarValueSingleByte(v)
    else if v <= 2047 then
      EncodeScalarValueDoubleByte(v)
    else if v <= 65535 then
      EncodeScalarValueTripleByte(v)
    else
      EncodeScalarValueQuadrupleByte(v)
  }

  function EncodeScalarValueSingleByte(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 0 <= v <= 127
    ensures |m| == 1
    ensures IsWellFormedSingleCodeUnitSequence(m)
  {
    var x := (v & 127) as bv7;
    var firstByte := x as CodeUnit;
    [firstByte]
  }

  function EncodeScalarValueDoubleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 128 <= v <= 2047
    ensures |s| == 2
    ensures IsWellFormedDoubleCodeUnitSequence(s)
  {
    var x := (v & 63) as bv6;
    var y := (v & 1984 >> 6) as bv5;
    var firstByte := 192 | y as CodeUnit;
    var secondByte := 128 | x as CodeUnit;
    [firstByte, secondByte]
  }

  function EncodeScalarValueTripleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 2048 <= v <= 65535
    ensures |s| == 3
    ensures IsWellFormedTripleCodeUnitSequence(s)
  {
    var x := (v & 63) as bv6;
    var y := (v & 4032 >> 6) as bv6;
    var z := (v & 61440 >> 12) as bv4;
    var firstByte := 224 | z as CodeUnit;
    var secondByte := 128 | y as CodeUnit;
    var thirdByte := 128 | x as CodeUnit;
    [firstByte, secondByte, thirdByte]
  }

  function EncodeScalarValueQuadrupleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 65536 <= v <= 1114111
    ensures |s| == 4
    ensures IsWellFormedQuadrupleCodeUnitSequence(s)
  {
    assert v <= 2097151;
    var x := (v & 63) as bv6;
    var y := (v & 4032 >> 6) as bv6;
    var z := (v & 61440 >> 12) as bv4;
    var u2 := (v & 196608 >> 16) as bv2;
    var u1 := (v & 1835008 >> 18) as bv3;
    var firstByte := 240 | u1 as CodeUnit;
    var secondByte := 128 | (u2 as CodeUnit << 4) | z as CodeUnit;
    var thirdByte := 128 | y as CodeUnit;
    var fourthByte := 128 | x as CodeUnit;
    [firstByte, secondByte, thirdByte, fourthByte]
  }

  function DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
  {
    if |m| == 1 then
      DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m)
    else if |m| == 2 then
      DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m)
    else if |m| == 3 then
      DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m)
    else
      assert |m| == 4; DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m)
  }

  function DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 1
    ensures 0 <= v <= 127
    ensures EncodeScalarValueSingleByte(v) == m
  {
    var firstByte := m[0];
    var x := firstByte as bv7;
    x as Unicode.ScalarValue
  }

  function DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 2
    ensures 128 <= v <= 2047
    ensures EncodeScalarValueDoubleByte(v) == m
  {
    var firstByte := m[0];
    var secondByte := m[1];
    var y := (firstByte & 31) as bv24;
    var x := (secondByte & 63) as bv24;
    (y << 6) | x as Unicode.ScalarValue
  }

  function DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 3
    ensures 2048 <= v <= 65535
    ensures EncodeScalarValueTripleByte(v) == m
  {
    var firstByte := m[0];
    var secondByte := m[1];
    var thirdByte := m[2];
    var z := (firstByte & 15) as bv24;
    var y := (secondByte & 63) as bv24;
    var x := (thirdByte & 63) as bv24;
    assert {:split_here} true;
    (z << 12) | (y << 6) | x as Unicode.ScalarValue
  }

  function DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 4
    ensures 65536 <= v <= 1114111
    ensures EncodeScalarValueQuadrupleByte(v) == m
  {
    var firstByte := m[0];
    var secondByte := m[1];
    var thirdByte := m[2];
    var fourthByte := m[3];
    var u1 := (firstByte & 7) as bv24;
    var u2 := (secondByte & 48 >> 4) as bv24;
    var z := (secondByte & 15) as bv24;
    var y := (thirdByte & 63) as bv24;
    var x := (fourthByte & 63) as bv24;
    assert {:split_here} true;
    (u1 << 18) | (u2 << 16) | (z << 12) | (y << 6) | x as Unicode.ScalarValue
  }

  type CodeUnit = bv8
}
