
// ExpandedGuardedness.dfy

method Main()
{
  PrintStream("Up", Up(19));
  PrintStream("Up2", Up2(19));
  PrintStream("UpIf", UpIf(19));
  PrintStream("CUp1", CUp1(19, Blue));
  PrintStream("UpLet0", UpLet0(19));
  PrintStream("UpLet1", UpLet1(19));
  var l := OnlyDs();
  var s := "";
  while |s| < 6
    invariant l == OnlyDs() || l == Nothing()
  {
    print s, if l.nullable then "  yes\n" else "  no\n";
    var ch := if |s| < 3 then 'D' else 'v';
    l := l.deriv(ch);
    s := s + [ch];
  }
  GhostMain();
  var ml := MOnlyDs();
  s := "";
  while |s| < 6
    invariant ml == MOnlyDs() || ml == MNothing()
  {
  }
}

method PrintStream(tag: string, s: Stream<int>)
{
  print tag;
  var n, s := 0, s;
  while n < 5 {
    print " ", s.head;
    s, n := s.tail, n + 1;
  }
  print "\n";
}

ghost method GhostMain()
{
  var l := IMOnlyDs();
  var s := "";
  while |s| < 6 {
    var ch := if |s| < 3 then 'D' else 'v';
    l := if ch in l.deriv.Keys then l.deriv[ch] else IML(false, l.deriv);
    s := s + [ch];
  }
}

function Up(n: int): Stream<int>
{
  ICons(n, Up(n + 1))
}

function Up2(n: int): Stream<int>
{
  ICons(n, ICons(n + 1, Up2(n + 2)))
}

function UpIf(n: int): Stream<int>
{
  if n % 2 == 1 then
    ICons(n, UpIf(n + 1))
  else
    ICons(n, UpIf(n + 2))
}

function UpIf'(n: int): Stream<int>
{
  ICons(n, if n % 2 == 1 then UpIf'(n + 1) else UpIf'(n + 2))
}

function CUp0(n: int, c: Color): Stream<int>
{
  match c
  case Red =>
    ICons(n, CUp0(n + 1, c))
  case Blue =>
    ICons(n, CUp0(n + 2, c))
}

function CUp1(n: int, c: Color): Stream<int>
{
  ICons(n, match c case Red => CUp1(n + 1, c) case Blue => CUp1(n + 2, c))
}

function CUp2(n: int, c: Color): Stream<int>
{
  if c == Red then
    ICons(n, CUp2(n + 1, c))
  else
    ICons(n, CUp2(n + 2, c))
}

function CUp3(n: int, c: Color): Stream<int>
{
  ICons(n, if c == Red then CUp3(n + 1, c) else CUp3(n + 2, c))
}

greatest lemma CUps(n: int, c: Color)
  ensures CUp0(n, c) == CUp1(n, c) == CUp2(n, c) == CUp3(n, c)
{
}

function UpLet0(n: int): Stream<int>
{
  var n' := n + 1;
  ICons(n' - 1, UpLet0(n'))
}

function UpLet1(n: int): Stream<int>
{
  ICons(n, var n' := n + 1; UpLet1(n'))
}

function Nothing(): Lang
{
  L(false, s => Nothing())
}

function OnlyDs(): Lang<char>
{
  L(true, ch => if ch == 'd' || ch == 'D' then OnlyDs() else Nothing())
}

greatest predicate TotalLang<S(!new)>(l: Lang<S>)
  reads *
{
  forall s: S :: 
    l.deriv.requires(s) &&
    l.deriv.reads(s) == {} &&
    TotalLang(l.deriv(s))
}

greatest lemma NothingTotal<S>()
  ensures TotalLang(Nothing<S>())
{
}

greatest lemma OnlyDsTotal()
  ensures TotalLang(OnlyDs())
{
  NothingTotal<char>();
  OnlyDsTotal();
}

greatest predicate TotalLang_Nat<S(!new)>[nat](l: Lang<S>)
  reads *
{
  forall s: S :: 
    l.deriv.requires(s) &&
    l.deriv.reads(s) == {} &&
    TotalLang_Nat(l.deriv(s))
}

greatest lemma NothingTotal_Nat<S>[nat]()
  ensures TotalLang_Nat(Nothing<S>())
{
}

greatest lemma OnlyDsTotal_Nat[nat]()
  ensures TotalLang_Nat(OnlyDs())
{
  OnlyDsTotal_Nat();
}

ghost function IMNothing<S(!new)>(): IMLang
{
  IML(false, imap s {:nowarn} | true :: IMNothing())
}

ghost function IMOnlyDs(): IMLang<char>
{
  IML(true, imap ch {:nowarn} | true :: if ch == 'd' || ch == 'D' then IMOnlyDs() else IMNothing())
}

function MNothing(): MLang
{
  ML(false, map s {:nowarn} | s in {} :: MNothing())
}

function MOnlyDs(): MLang<char>
{
  ML(true, map ch {:nowarn} | ch == 'd' || ch == 'D' :: MOnlyDs())
}

codatatype Stream<T> = ICons(head: T, tail: Stream<T>)

datatype Color = Red | Blue

codatatype Lang<!S> = L(nullable: bool, deriv: S ~> Lang<S>)

codatatype IMLang<!S> = IML(nullable: bool, deriv: imap<S, IMLang<S>>)

codatatype MLang<S> = ML(nullable: bool, deriv: map<S, MLang<S>>)
