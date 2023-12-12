
// git-issue195.dfy

function GenesisBlock(): Block<int, int, int>
{
  Block(0, [], 0)
}

method IsGenesisBlock(b: Block<int, int, int>) returns (eq: bool)
  ensures eq <==> b == GenesisBlock()
{
  var gb := GenesisBlock();
  eq := b == gb;
}

method Main()
{
  var b := GenesisBlock();
  var eq := IsGenesisBlock(b);
  assert eq;
  print eq, "\n";
  TestEq();
}

predicate TestAny<G(==)>(a: G, b: G)
  requires a == b
{
  a == b
}

method TestEq()
{
}

datatype Block<Hash, Transaction, VProof> = Block(prevBlockHash: Hash, txs: seq<Transaction>, proof: VProof)

newtype nt = int

newtype ntNative = x
  | -100 <= x < 100

class MyClass {
  var u: int
}

datatype X = X(bool, char, int, real, nt, ntNative, bv8, bv167, ORDINAL, MyClass)
