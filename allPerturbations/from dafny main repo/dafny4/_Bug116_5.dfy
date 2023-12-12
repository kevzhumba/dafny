
// Bug116.dfy

method Main()
{
  var s := S;
  var t: struct;
  var b := arguments;
  var ref: enum.goto, transient: enum.goto;
  ref := enum.switch;
  transient := enum.do();
  print ref, " ", transient, "\n";
  var params := catch(20);
  var final := enum.catch(params);
  var procedure := params + final;
  print params, " + ", final, " == ", procedure, "\n";
}

method catch(do: int) returns (finally: int)
{
  finally := do;
}

datatype struct = S

datatype byte = arguments

module enum {
  function do(): goto
  {
    switch
  }

  method catch(do: int) returns (finally: int)
  {
    finally := do;
  }

  datatype goto = switch
}
