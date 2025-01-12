
// git-issue176.dfy

ghost predicate Thing1()
{
  var m := map[0 := 1];
  forall i :: 
    i in m ==>
      i == 0
}

ghost predicate Thing2(ctx: Context)
{
  var ctx' := ctx.(foo := map[0 := 1]);
  forall i :: 
    i in ctx'.foo ==>
      i == 0
}

method Main()
{
  assert Thing1();
}

datatype Context = Context(foo: map<int, int>)
