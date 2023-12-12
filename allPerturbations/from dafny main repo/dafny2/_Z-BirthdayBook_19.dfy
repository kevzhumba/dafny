
// Z-BirthdayBook.dfy

method Main()
{
}

abstract module Specification {
  const John: Name
  const Mike: Name
  const Susan: Name
  const Mar25: Date
  const Dec20: Date

  type Name(==)

  type Date

  class {:autocontracts} BirthdayBook {
    var known: set<Name>
    var birthday: map<Name, Date>

    ghost predicate Valid()
    {
      known == birthday.Keys
    }

    method AddBirthday(name: Name, date: Date)
      requires name !in known
      modifies this
      ensures birthday == old(birthday)[name := date]

    method ConsequenceOfAddBirthday(name: Name, date: Date)
      requires name !in known
    {
      AddBirthday(name, date);
      assert known == old(known) + {name};
      calc {
        known;
      ==
        {
          assert Valid();
        }
        birthday.Keys;
      ==
        old(birthday)[name := date].Keys;
      ==
        old(birthday).Keys + map[name := date].Keys;
      ==
        old(birthday).Keys + {name};
      ==
        {
          assert old(Valid());
        }
        old(known) + {name};
      }
    }

    method FindBirthday(name: Name) returns (date: Date)
      requires name in known
      ensures unchanged(this)
      ensures date == birthday[name]

    method Remind(today: Date) returns (cards: set<Name>)
      ensures unchanged(this)
      ensures cards == set n | n in known && birthday[n] == today

    method ConsequenceOfRemind(today: Date, m: Name)
    {
      var cards := Remind(today);
      assert m in cards <==> m in known && birthday[m] == today;
    }

    constructor Init()
      ensures known == {}

    method ConsequenceOfInit()
    {
      var bb := new BirthdayBook.Init();
      assert bb.birthday == map[];
    }
  }
}

module Implementation refines Specification {
  const John := "John"
  const Mike := "Mike"
  const Susan := "Susan"
  const Mar25 := 325
  const Dec20 := 1220

  type Name = string

  type Date = int

  class BirthdayBook ... {
    method AddBirthday ...
    {
      known := known + {name};
      birthday := birthday[name := date];
    }

    method FindBirthday(name: Name) returns (date: Date)
    {
      date := birthday[name];
    }

    method Remind(today: Date) returns (cards: set<Name>)
    {
      cards := set n | n in known && birthday[n] == today;
    }

    constructor Init ...
    {
      known, birthday := {}, map[];
      Repr := {this};
    }
  }
}
