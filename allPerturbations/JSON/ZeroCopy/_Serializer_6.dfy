include "../Utils/Seq.dfy"
include "../Errors.dfy"
include "../ConcreteSyntax.Spec.dfy"
include "../ConcreteSyntax.SpecProperties.dfy"
include "../Utils/Views.Writers.dfy"
// Serializer.dfy


module JSON {

  module ZeroCopy {

    module {:options "-functionSyntax:4"} Serializer {
      method Serialize(js: JSON) returns (rbs: SerializationResult<array<byte>>)
        ensures rbs.Success? ==> fresh(rbs.value)
        ensures rbs.Success? ==> rbs.value[..] == Spec.JSON(js)
      {
        var writer := Text(js);
        :- Need(writer.Unsaturated?, OutOfMemory);
        var bs := writer.ToArray();
        return Success(bs);
      }

      method SerializeTo(js: JSON, dest: array<byte>) returns (len: SerializationResult<uint32>)
        modifies dest
        ensures len.Success? ==> len.value as int <= dest.Length
        ensures len.Success? ==> dest[..len.value] == Spec.JSON(js)
        ensures len.Success? ==> dest[len.value..] == old(dest[len.value..])
        ensures len.Failure? ==> unchanged(dest)
      {
        var writer := Text(js);
        :- Need(writer.Unsaturated?, OutOfMemory);
        writer.CopyTo(dest);
        return Success(writer.length);
      }

      function {:opaque} Text(js: JSON): (wr: Writer)
        ensures wr.Bytes() == Spec.JSON(js)
      {
        JSON(js)
      }

      function {:opaque} JSON(js: JSON, writer: Writer := Writer.Empty): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.JSON(js)
      {
        Seq.Assoc2(writer.Bytes(), js.before.Bytes(), Spec.Value(js.t), js.after.Bytes());
        writer.Append(js.before).Then(wr => Value(js.t, wr)).Append(js.after)
      }

      function {:opaque} {:vcs_split_on_every_assert} Value(v: Value, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
        decreases v, 4
      {
        match v
        case Null(n) =>
          writer.Append(n)
        case Bool(b) =>
          var wr := writer.Append(b);
          wr
        case String(str) =>
          var wr := String(str, writer);
          wr
        case Number(num) =>
          assert Grammar.Number(num) == v by {
            Spec.UnfoldValueNumber(v);
          } var wr := Number(num, writer); wr
        case Object(obj) =>
          assert Grammar.Object(obj) == v; assert Spec.Value(v) == Spec.Value(Grammar.Object(obj)) == Spec.Object(obj); var wr := Object(obj, writer); wr
        case Array(arr) =>
          assert Grammar.Array(arr) == v;
          assert Spec.Value(v) == Spec.Array(arr);
          var wr := Array(arr, writer);
          assert wr.Bytes() == writer.Bytes() + Spec.Value(v);
          wr
      }

      function {:opaque} String(str: jstring, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.String(str)
        decreases str, 0
      {
        writer.Append(str.lq).Append(str.contents).Append(str.rq)
      }

      function {:opaque} {:vcs_split_on_every_assert} Number(num: jnumber, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Number(num)
        decreases num, 0
      {
        var wr := writer.Append(num.minus).Append(num.num);
        var wr := if num.frac.NonEmpty? then wr.Append(num.frac.t.period).Append(num.frac.t.num) else wr;
        assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac) by {
          assert num.frac.Empty? ==> wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + [];
        }
        var wr := if num.exp.NonEmpty? then wr.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num) else wr;
        assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp) by {
          if num.exp.NonEmpty? {
          } else {
            assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac) + [];
          }
        }
        wr
      }

      function StructuralView(st: Structural<View>, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
      {
        writer.Append(st.before).Append(st.t).Append(st.after)
      }

      lemma StructuralViewEns(st: Structural<View>, writer: Writer)
        ensures StructuralView(st, writer).Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
      {
      }

      lemma {:axiom} Assume(b: bool)
        ensures b

      lemma BracketedToObject(obj: jobject)
        ensures Spec.Bracketed(obj, Spec.Member) == Spec.Object(obj)
      {
        var rMember := (d: jmember) requires d < obj => Spec.Member(d);
        assert Spec.Bracketed(obj, Spec.Member) == Spec.Bracketed(obj, rMember) by {
          assert SpecProperties.Bracketed_Morphism_Requires(obj, Spec.Member, rMember);
          SpecProperties.Bracketed_Morphism(obj, Spec.Member, rMember);
        }
        calc {
          Spec.Bracketed(obj, Spec.Member);
          Spec.Bracketed(obj, rMember);
          Spec.Object(obj);
        }
      }

      function {:opaque} Object(obj: jobject, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Object(obj)
        decreases obj, 3
      {
        var wr := StructuralView(obj.l, writer);
        StructuralViewEns(obj.l, writer);
        var wr := Members(obj, wr);
        var wr := StructuralView(obj.r, wr);
        Seq.Assoc2(writer.Bytes(), Spec.Structural<View>(obj.l, Spec.View), Spec.ConcatBytes(obj.data, Spec.Member), Spec.Structural<View>(obj.r, Spec.View));
        assert wr.Bytes() == writer.Bytes() + Spec.Bracketed(obj, Spec.Member);
        assert Spec.Bracketed(obj, Spec.Member) == Spec.Object(obj) by {
          BracketedToObject(obj);
        }
        wr
      }

      lemma BracketedToArray(arr: jarray)
        ensures Spec.Bracketed(arr, Spec.Item) == Spec.Array(arr)
      {
        var rItem := (d: jitem) requires d < arr => Spec.Item(d);
        assert Spec.Bracketed(arr, Spec.Item) == Spec.Bracketed(arr, rItem) by {
          assert SpecProperties.Bracketed_Morphism_Requires(arr, Spec.Item, rItem);
          SpecProperties.Bracketed_Morphism(arr, Spec.Item, rItem);
        }
        calc {
          Spec.Bracketed(arr, Spec.Item);
          Spec.Bracketed(arr, rItem);
          Spec.Array(arr);
        }
      }

      function {:opaque} Array(arr: jarray, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Array(arr)
        decreases arr, 3
      {
        var wr := StructuralView(arr.l, writer);
        StructuralViewEns(arr.l, writer);
        var wr := Items(arr, wr);
        var wr := StructuralView(arr.r, wr);
        Seq.Assoc2(writer.Bytes(), Spec.Structural<View>(arr.l, Spec.View), Spec.ConcatBytes(arr.data, Spec.Item), Spec.Structural<View>(arr.r, Spec.View));
        assert wr.Bytes() == writer.Bytes() + Spec.Bracketed(arr, Spec.Item);
        assert Spec.Bracketed(arr, Spec.Item) == Spec.Array(arr) by {
          BracketedToArray(arr);
        }
        wr
      }

      function {:opaque} Members(obj: jobject, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(obj.data, Spec.Member)
        decreases obj, 2
      {
        MembersSpec(obj, obj.data, writer)
      } by method {
        wr := MembersImpl(obj, writer);
        Assume(false);
      }

      function {:opaque} Items(arr: jarray, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(arr.data, Spec.Item)
        decreases arr, 2
      {
        ItemsSpec(arr, arr.data, writer)
      } by method {
        wr := ItemsImpl(arr, writer);
        Assume(false);
      }

      ghost function MembersSpec(obj: jobject, members: seq<jmember>, writer: Writer): (wr: Writer)
        requires forall j | 0 <= j < |members| :: members[j] < obj
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(members, Spec.Member)
        decreases obj, 1, members
      {
        if members == [] then
          writer
        else
          var butLast, last := members[..|members| - 1], members[|members| - 1]; assert members == butLast + [last]; var wr := MembersSpec(obj, butLast, writer); var wr := Member(obj, last, wr); assert wr.Bytes() == writer.Bytes() + (Spec.ConcatBytes(butLast, Spec.Member) + Spec.ConcatBytes([last], Spec.Member)) by {
    Seq.Assoc(writer.Bytes(), Spec.ConcatBytes(butLast, Spec.Member), Spec.ConcatBytes([last], Spec.Member));
  } SpecProperties.ConcatBytes_Linear(butLast, [last], Spec.Member); wr
      }

      ghost function SequenceSpec<T>(v: Value, items: seq<T>, spec: T -> bytes, impl: (Value, T, Writer) --> Writer, writer: Writer): (wr: Writer)
        requires forall item, wr | item in items :: impl.requires(v, item, wr)
        requires forall item, wr | item in items :: impl(v, item, wr).Bytes() == wr.Bytes() + spec(item)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, spec)
        decreases v, 1, items
      {
        if items == [] then
          writer
        else
          var writer := SequenceSpec(v, items[..|items| - 1], spec, impl, writer); assert items == items[..|items| - 1] + [items[|items| - 1]]; SpecProperties.ConcatBytes_Linear(items[..|items| - 1], [items[|items| - 1]], spec); impl(v, items[|items| - 1], writer)
      }

      ghost function ItemsSpec(arr: jarray, items: seq<jitem>, writer: Writer): (wr: Writer)
        requires forall j | 0 <= j < |items| :: items[j] < arr
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, Spec.Item)
        decreases arr, 1, items
      {
        if items == [] then
          writer
        else
          var butLast, last := items[..|items| - 1], items[|items| - 1]; assert items == butLast + [last]; var wr := ItemsSpec(arr, butLast, writer); var wr := Item(arr, last, wr); assert wr.Bytes() == writer.Bytes() + (Spec.ConcatBytes(butLast, Spec.Item) + Spec.ConcatBytes([last], Spec.Item)) by {
    Seq.Assoc(writer.Bytes(), Spec.ConcatBytes(butLast, Spec.Item), Spec.ConcatBytes([last], Spec.Item));
  } SpecProperties.ConcatBytes_Linear(butLast, [last], Spec.Item); wr
      }

      method MembersImpl(obj: jobject, writer: Writer) returns (wr: Writer)
        ensures wr == MembersSpec(obj, obj.data, writer)
        decreases obj, 1
      {
        wr := writer;
        var members := obj.data;
        assert wr == MembersSpec(obj, members[..0], writer);
        for i := 0 to |members|
          invariant wr == MembersSpec(obj, members[..i], writer)
        {
          assert members[..i + 1][..i] == members[..i];
          wr := Member(obj, members[i], wr);
        }
        assert members[..|members|] == members;
        assert wr == MembersSpec(obj, members, writer);
      }

      method {:vcs_split_on_every_assert} ItemsImpl(arr: jarray, writer: Writer) returns (wr: Writer)
        ensures wr == ItemsSpec(arr, arr.data, writer)
        decreases arr, 1
      {
        wr := writer;
        var items := arr.data;
        assert wr == ItemsSpec(arr, items[..0], writer);
        for i := 0 to |items|
          invariant wr == ItemsSpec(arr, items[..i], writer)
        {
          assert items[..i + 1][..i] == items[..i] by {
            AboutList(items, i, i + 1);
          }
          wr := Item(arr, items[i], wr);
        }
        assert items[..|items|] == items;
      }

      lemma AboutList<T>(xs: seq<T>, i: nat, j: nat)
        requires i < j <= |xs|
        ensures xs[..j][..i] == xs[..i]
      {
      }

      function {:opaque} Member(ghost obj: jobject, m: jmember, writer: Writer): (wr: Writer)
        requires m < obj
        ensures wr.Bytes() == writer.Bytes() + Spec.Member(m)
        decreases obj, 0
      {
        var wr := String(m.t.k, writer);
        var wr := StructuralView(m.t.colon, wr);
        var wr := Value(m.t.v, wr);
        assert wr.Bytes() == writer.Bytes() + (Spec.String(m.t.k) + Spec.Structural<View>(m.t.colon, Spec.View) + Spec.Value(m.t.v)) by {
          Seq.Assoc2(writer.Bytes(), Spec.String(m.t.k), Spec.Structural<View>(m.t.colon, Spec.View), Spec.Value(m.t.v));
        }
        var wr := if m.suffix.Empty? then wr else StructuralView(m.suffix.t, wr);
        assert wr.Bytes() == writer.Bytes() + Spec.KeyValue(m.t) + Spec.CommaSuffix(m.suffix) by {
          if m.suffix.Empty? {
            Neutral(Spec.KeyValue(m.t));
            Seq.Assoc'(writer.Bytes(), Spec.KeyValue(m.t), []);
          } else {
            assert Spec.StructuralView(m.suffix.t) == Spec.CommaSuffix(m.suffix);
          }
        }
        assert wr.Bytes() == writer.Bytes() + (Spec.KeyValue(m.t) + Spec.CommaSuffix(m.suffix)) by {
          Seq.Assoc(writer.Bytes(), Spec.KeyValue(m.t), Spec.CommaSuffix(m.suffix));
        }
        wr
      }

      function {:opaque} Item(ghost arr: jarray, m: jitem, writer: Writer): (wr: Writer)
        requires m < arr
        ensures wr.Bytes() == writer.Bytes() + Spec.Item(m)
        decreases arr, 0
      {
        var wr := Value(m.t, writer);
        var wr := if m.suffix.Empty? then wr else StructuralView(m.suffix.t, wr);
        assert wr.Bytes() == writer.Bytes() + (Spec.Value(m.t) + Spec.CommaSuffix(m.suffix)) by {
          Seq.Assoc(writer.Bytes(), Spec.Value(m.t), Spec.CommaSuffix(m.suffix));
        }
        wr
      }

      import opened BoundedInts

      import opened Wrappers

      import opened Seq = Utils.Seq

      import opened Errors

      import Spec = ConcreteSyntax.Spec

      import SpecProperties = ConcreteSyntax.SpecProperties

      import opened Grammar

      import opened Writers = Utils.Views.Writers

      import opened Vs = Utils.Views.Core
    }
  }
}
