
// Bug104.dfy

method UpdateField()
{
  var v := PartRealPartGhost(3, 4);
  ghost var g := 5;
}

datatype PartRealPartGhost = PartRealPartGhost(x: int, ghost y: int)
