
// Bug148.dfy

method Main()
{
  var zero: real := 0.0;
  var three: real := 3.0;
  var fifteen: real := 15.0;
  var negone: real := -1.0;
  var negthree: real := -3.0;
  print zero <= fifteen, "\n";
  print fifteen <= zero, "\n";
  print negone <= zero, "\n";
  print negone <= fifteen, "\n";
  print fifteen <= negone, "\n";
  print zero >= fifteen, "\n";
  print fifteen >= zero, "\n";
  print negone >= zero, "\n";
  print zero >= negone, "\n";
  print negone >= fifteen, "\n";
  print fifteen >= negone, "\n";
}
