
// consoleio.dfy

method {:axiom} WriteLine(line: string)

method {:axiom} ReadLine() returns (line: string)

method {:main} Main()
{
  var name := ReadLine();
  WriteLine("hello, " + name + "!");
}