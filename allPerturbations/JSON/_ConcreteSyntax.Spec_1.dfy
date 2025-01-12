include "Grammar.dfy"
// ConcreteSyntax.Spec.dfy


module JSON {

  module ConcreteSyntax {

    module {:options "-functionSyntax:4"} Spec {
      function View(v: Vs.View): bytes
      {
        v.Bytes()
      }

      function Structural<T>(self: Structural<T>, fT: T -> bytes): bytes
      {
        View(self.before) + fT(self.t) + View(self.after)
      }

      function StructuralView(self: Structural<Vs.View>): bytes
      {
        Structural<Vs.View>(self, View)
      }

      function Maybe<T>(self: Maybe<T>, fT: T -> bytes): (bs: bytes)
        ensures self.Empty? ==> bs == []
        ensures self.NonEmpty? ==> bs == fT(self.t)
      {
        if self.Empty? then
          []
        else
          fT(self.t)
      }

      function ConcatBytes<T>(ts: seq<T>, fT: T --> bytes): bytes
        requires forall d | d in ts :: fT.requires(d)
      {
        if |ts| == 0 then
          []
        else
          fT(ts[0]) + ConcatBytes(ts[1..], fT)
      }

      function Bracketed<D, S>(self: Bracketed<Vs.View, D, S, Vs.View>, fDatum: Suffixed<D, S> --> bytes): bytes
        requires forall d | d < self :: fDatum.requires(d)
      {
        StructuralView(self.l) + ConcatBytes(self.data, fDatum) + StructuralView(self.r)
      }

      function KeyValue(self: jKeyValue): bytes
      {
        String(self.k) + StructuralView(self.colon) + Value(self.v)
      }

      function Frac(self: jfrac): bytes
      {
        View(self.period) + View(self.num)
      }

      function Exp(self: jexp): bytes
      {
        View(self.e) + View(self.sign) + View(self.num)
      }

      function Number(self: jnumber): bytes
      {
        View(self.minus) + View(self.num) + Maybe(self.frac, Frac) + Maybe(self.exp, Exp)
      }

      function String(self: jstring): bytes
      {
        View(self.lq) + View(self.contents) + View(self.rq)
      }

      function CommaSuffix(c: Maybe<Structural<jcomma>>): bytes
      {
        Maybe<Structural<Vs.View>>(c, StructuralView)
      }

      function Member(self: jmember): bytes
      {
        KeyValue(self.t) + CommaSuffix(self.suffix)
      }

      function Item(self: jitem): bytes
      {
        Value(self.t) + CommaSuffix(self.suffix)
      }

      function Object(obj: jobject): bytes
      {
        Bracketed(obj, (d: jmember) requires d < obj => Member(d))
      }

      function Array(arr: jarray): bytes
      {
        Bracketed(arr, (d: jitem) requires d < arr => Item(d))
      }

      function Value(self: Value): bytes
      {
        match self {
          case Null(n) =>
            View(n)
          case Bool(b) =>
            View(b)
          case String(str) =>
            String(str)
          case Number(num) =>
            Number(num)
          case Object(obj) =>
            Object(obj)
          case Array(arr) =>
            Array(arr)
        }
      }

      lemma UnfoldValueNumber(v: Value)
        requires v.Number?
        ensures Value(v) == Number(v.num)
      {
      }

      lemma UnfoldValueObject(v: Value)
        requires v.Object?
        ensures Value(v) == Object(v.obj)
      {
        assert Value(v) == match v { case Object(obj) => Object(obj) case _ /* _v1 */ => [] };
      }

      lemma UnfoldValueArray(v: Value)
        requires v.Array?
        ensures Value(v) == Array(v.arr)
      {
        assert Value(v) == match v { case Array(arr) => Array(arr) case _ /* _v2 */ => [] };
      }

      function JSON(js: JSON): bytes
      {
        Structural(js, Value)
      }

      import opened BoundedInts

      import Vs = Utils.Views.Core

      import opened Grammar
    }
  }
}
