
// Circ.dfy

ghost function zeros(): Stream<int>
{
  Cons(0, zeros())
}

ghost function ones(): Stream<int>
{
  Cons(1, ones())
}

ghost function blink(): Stream<int>
{
  Cons(0, Cons(1, blink()))
}

ghost function zip(a: Stream, b: Stream): Stream
{
  Cons(a.head, zip(b, a.tail))
}

greatest lemma BlinkZipProperty()
  ensures zip(zeros(), ones()) == blink()
{
  BlinkZipProperty();
}

ghost function bitnot(b: Bit): Bit
{
  if b == O then
    I
  else
    O
}

ghost function not(s: Stream<Bit>): Stream<Bit>
{
  Cons(bitnot(s.head), not(s.tail))
}

ghost function morse(): Stream<Bit>

ghost function morseTail(): Stream<Bit>

lemma MorseProperties()
  ensures morse().head == O
  ensures morseTail() == morse().tail
  ensures morseTail().head == I
  ensures morseTail().tail == zip(morseTail(), not(morseTail()))

ghost function f(s: Stream<Bit>): Stream<Bit>
{
  Cons(s.head, Cons(bitnot(s.head), f(s.tail)))
}

greatest lemma FProperty(s: Stream<Bit>)
  ensures f(s) == zip(s, not(s))
{
}

lemma Fixpoint()
  ensures f(morse()) == morse()
{
  MorseProperties();
  FProperty(morseTail());
}

codatatype Stream<T> = Cons(head: T, tail: Stream)

datatype Bit = O | I
