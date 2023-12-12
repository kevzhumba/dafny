
// CoqArt-InsertionSort.dfy

ghost predicate sorted(l: List<int>)
{
  match l
  case Nil =>
    true
  case Cons(x, rest) =>
    match rest
    case Nil =>
      true
    case Cons(y, _ /* _v0 */) =>
      x <= y &&
      sorted(rest)
}

lemma example_sort_2357()
  ensures sorted(Cons(2, Cons(3, Cons(5, Cons(7, Nil)))))
{
}

lemma sorted_inv(z: int, l: List<int>)
  requires sorted(Cons(z, l))
  ensures sorted(l)
{
  match l {
    case {:split false} Nil =>
    case {:split false} Cons(_ /* _v1 */, _ /* _v2 */) =>
  }
}

ghost function nb_occ(z: int, l: List<int>): nat
{
  match l
  case Nil =>
    0
  case Cons(z', l') =>
    (if z == z' then 1 else 0) + nb_occ(z, l')
}

lemma example_nb_occ_0()
  ensures nb_occ(3, Cons(3, Cons(7, Cons(3, Nil)))) == 2
{
}

lemma example_nb_occ_1()
  ensures nb_occ(36725, Cons(3, Cons(7, Cons(3, Nil)))) == 0
{
}

ghost predicate equiv(l: List<int>, l': List<int>)
{
  forall z :: 
    nb_occ(z, l) == nb_occ(z, l')
}

lemma equiv_refl(l: List<int>)
  ensures equiv(l, l)
{
}

lemma equiv_sym(l: List<int>, l': List<int>)
  requires equiv(l, l')
  ensures equiv(l', l)
{
}

lemma equiv_trans(l: List<int>, l': List<int>, l'': List<int>)
  requires equiv(l, l') && equiv(l', l'')
  ensures equiv(l, l'')
{
}

lemma equiv_cons(z: int, l: List<int>, l': List<int>)
  requires equiv(l, l')
  ensures equiv(Cons(z, l), Cons(z, l'))
{
}

lemma equiv_perm(a: int, b: int, l: List<int>, l': List<int>)
  requires equiv(l, l')
  ensures equiv(Cons(a, Cons(b, l)), Cons(b, Cons(a, l')))
{
}

function aux(z: int, l: List<int>): List<int>
{
  match l
  case Nil =>
    Cons(z, Nil)
  case Cons(a, l') =>
    if z <= a then
      Cons(z, l)
    else
      Cons(a, aux(z, l'))
}

lemma example_aux_0()
  ensures aux(4, Cons(2, Cons(5, Nil))) == Cons(2, Cons(4, Cons(5, Nil)))
{
}

lemma example_aux_1()
  ensures aux(4, Cons(24, Cons(50, Nil))) == Cons(4, Cons(24, Cons(50, Nil)))
{
}

lemma aux_equiv(l: List<int>, x: int)
  ensures equiv(Cons(x, l), aux(x, l))
{
  match l {
    case {:split false} Nil =>
    case {:split false} Cons(_ /* _v3 */, _ /* _v4 */) =>
  }
}

lemma aux_sorted(l: List<int>, x: int)
  requires sorted(l)
  ensures sorted(aux(x, l))
{
  match l {
    case {:split false} Nil =>
    case {:split false} Cons(_ /* _v5 */, l') =>
      match l' {
        case {:split false} Nil =>
        case {:split false} Cons(_ /* _v6 */, _ /* _v7 */) =>
      }
  }
}

ghost function sort(l: List<int>): List<int>
  ensures var l' := sort(l); equiv(l, l') && sorted(l')
{
  existence_proof(l);
  var l' :| equiv(l, l') && sorted(l');
  l'
}

lemma existence_proof(l: List<int>)
  ensures exists l' :: equiv(l, l') && sorted(l')
{
  match l {
    case {:split false} Nil =>
      assert sorted(Nil);
    case {:split false} Cons(x, m) =>
      existence_proof(m);
      var m' :| equiv(m, m') && sorted(m');
      calc ==> {
        equiv(m, m') &&
        sorted(m');
        equiv(l, Cons(x, m')) &&
        sorted(m');
        {
          aux_equiv(m', x);
        }
        equiv(l, aux(x, m')) &&
        sorted(m');
        {
          aux_sorted(m', x);
        }
        equiv(l, aux(x, m')) &&
        sorted(aux(x, m'));
      }
  }
}

function Sort(l: List<int>): List<int>
  ensures equiv(l, Sort(l)) && sorted(Sort(l))
{
  match l
  case Nil =>
    l
  case Cons(x, m) =>
    var m' := Sort(m);
    assert equiv(l, Cons(x, m'));
    aux_equiv(m', x);
    aux_sorted(m', x);
    aux(x, m')
}

ghost predicate p_aux_equiv(l: List<int>, x: int)
  ensures equiv(Cons(x, l), aux(x, l))
{
  aux_equiv(l, x);
  true
}

ghost predicate p_aux_sorted(l: List<int>, x: int)
  requires sorted(l)
  ensures sorted(aux(x, l))
{
  aux_sorted(l, x);
  true
}

datatype List<T> = Nil | Cons(head: T, tail: List)
