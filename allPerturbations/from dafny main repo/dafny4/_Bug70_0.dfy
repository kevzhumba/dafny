
// Bug70.dfy


module M1 {
  datatype d = D
}

module M2 {

  import opened M1
}

module M3 {

  import opened M1
}

module M4 {
  method Main()
  {
  }

  import opened M1

  import opened M2

  import opened M3
}
