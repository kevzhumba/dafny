include "../Wrappers.dfy"
include "../Functions.dfy"
include "../Collections/Sequences/Seq.dfy"
include "Unicode.dfy"
// UnicodeEncodingForm.dfy


abstract module {:options "-functionSyntax:4"} UnicodeEncodingForm {
  function IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
    ensures b ==> |s| > 0 && forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases |s|

  function SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==> true && maybePrefix.Some?
    ensures maybePrefix.Some? ==> true && var prefix := maybePrefix.Extract(); 0 < |prefix| <= |s| && prefix == s[..|prefix|] && forall i | 0 < i < |prefix| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])

  function EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)

  function DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    ensures EncodeScalarValue(v) == m

  lemma LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m: MinimalWellFormedCodeUnitSeq, s: CodeUnitSeq)
    ensures SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + s) == Some(m)
  {
    var ms := m + s;
    assert IsMinimalWellFormedCodeUnitSubsequence(ms[..|m|]);
    var prefix := SplitPrefixMinimalWellFormedCodeUnitSubsequence(ms).Extract();
    calc ==> {
      IsMinimalWellFormedCodeUnitSubsequence(m);
      |prefix| <= |m|;
      prefix == ms[..|prefix|] == m[..|prefix|] == m;
    }
  }

  function PartitionCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeParts: Option<seq<MinimalWellFormedCodeUnitSeq>>)
    ensures maybeParts.Some? ==> Seq.Flatten(maybeParts.Extract()) == s
    decreases |s|
  {
    if s == [] then
      Some([])
    else
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(s); var restParts :- PartitionCodeUnitSequenceChecked(s[|prefix|..]); Some([prefix] + restParts)
  } by method {
    if s == [] {
      return Some([]);
    }
    var result: seq<MinimalWellFormedCodeUnitSeq> := [];
    var rest := s;
    while |rest| > 0
      invariant PartitionCodeUnitSequenceChecked(s).Some? <==> PartitionCodeUnitSequenceChecked(rest).Some?
      invariant PartitionCodeUnitSequenceChecked(s).Some? ==> true && PartitionCodeUnitSequenceChecked(s).value == result + PartitionCodeUnitSequenceChecked(rest).value
    {
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(rest);
      result := result + [prefix];
      rest := rest[|prefix|..];
    }
    assert result + [] == result;
    return Some(result);
  }

  function PartitionCodeUnitSequence(s: WellFormedCodeUnitSeq): (parts: seq<MinimalWellFormedCodeUnitSeq>)
    ensures Seq.Flatten(parts) == s
  {
    PartitionCodeUnitSequenceChecked(s).Extract()
  }

  lemma LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq)
    ensures PartitionCodeUnitSequenceChecked(m) == Some([m])
  {
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, []);
    calc == {
      Some(m);
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + []);
      {
        assert m + [] == m;
      }
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m);
    }
    calc == {
      PartitionCodeUnitSequenceChecked(m);
      Some([m] + []);
      {
        assert [m] + [] == [m];
      }
      Some([m]);
    }
  }

  function IsWellFormedCodeUnitSequence(s: CodeUnitSeq): (b: bool)
  {
    PartitionCodeUnitSequenceChecked(s).Some?
  }

  lemma LemmaMinimalWellFormedCodeUnitSubsequenceIsWellFormedSequence(m: MinimalWellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m)
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
  }

  lemma LemmaPrependMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq, s: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m + s)
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, s);
    assert PartitionCodeUnitSequenceChecked(m + s).Some?;
  }

  lemma LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms: seq<MinimalWellFormedCodeUnitSeq>)
    ensures IsWellFormedCodeUnitSequence(Seq.Flatten(ms))
  {
    if |ms| == 1 {
      assert IsWellFormedCodeUnitSequence(Seq.Flatten(ms));
    } else {
      var head := ms[0];
      var tail := ms[1..];
      LemmaFlattenMinimalWellFormedCodeUnitSubsequences(tail);
      var flatTail := Seq.Flatten(tail);
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(head, flatTail);
      assert IsWellFormedCodeUnitSequence(head + flatTail);
    }
  }

  lemma LemmaConcatWellFormedCodeUnitSubsequences(s: WellFormedCodeUnitSeq, t: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(s + t)
  {
    var partsS := PartitionCodeUnitSequence(s);
    var partsT := PartitionCodeUnitSequence(t);
    var partsST := partsS + partsT;
    Seq.LemmaFlattenConcat(partsS, partsT);
    assert s + t == Seq.Flatten(partsST);
    assert forall part | part in partsST :: |part| > 0 && IsMinimalWellFormedCodeUnitSubsequence(part);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(partsST);
  }

  function EncodeScalarSequence(vs: seq<Unicode.ScalarValue>): (s: WellFormedCodeUnitSeq)
  {
    var ms := Seq.Map(EncodeScalarValue, vs);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms);
    Seq.Flatten(ms)
  } by method {
    s := [];
    ghost var unflattened: seq<MinimalWellFormedCodeUnitSeq> := [];
    for i := |vs| downto 0
      invariant unflattened == Seq.Map(EncodeScalarValue, vs[i..])
      invariant s == Seq.Flatten(unflattened)
    {
      var next: MinimalWellFormedCodeUnitSeq := EncodeScalarValue(vs[i]);
      unflattened := [next] + unflattened;
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(next, s);
      s := next + s;
    }
  }

  function DecodeCodeUnitSequence(s: WellFormedCodeUnitSeq): (vs: seq<Unicode.ScalarValue>)
    ensures EncodeScalarSequence(vs) == s
  {
    var parts := PartitionCodeUnitSequence(s);
    var vs := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    vs
  }

  function DecodeCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeVs: Option<seq<Unicode.ScalarValue>>)
    ensures IsWellFormedCodeUnitSequence(s) ==> maybeVs.Some? && maybeVs.Extract() == DecodeCodeUnitSequence(s)
    ensures !IsWellFormedCodeUnitSequence(s) ==> true && maybeVs.None?
  {
    if IsWellFormedCodeUnitSequence(s) then
      Some(DecodeCodeUnitSequence(s))
    else
      None
  } by method {
    var maybeParts := PartitionCodeUnitSequenceChecked(s);
    if maybeParts.None? {
      return None;
    }
    var parts := maybeParts.value;
    var vs := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    return Some(vs);
  }

  import opened Wrappers

  import Functions

  import Seq

  import Unicode

  type CodeUnitSeq = seq<CodeUnit>

  type WellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsWellFormedCodeUnitSequence(s)
    witness []

  type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsMinimalWellFormedCodeUnitSubsequence(s)
    witness *

  type CodeUnit
}
