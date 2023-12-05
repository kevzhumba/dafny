using System.Collections.Generic;

namespace Microsoft.Dafny.Perturber;

public class CfgUtil {

  public static ISet<CfgToAstTransformer.CFGNode> DFS(CfgToAstTransformer.CFGNode head, CfgToAstTransformer.CFGNode entry, CfgToAstTransformer.CFGNode exit) {
    Stack<CfgToAstTransformer.CFGNode> stack = new Stack<CfgToAstTransformer.CFGNode>();
    ISet<CfgToAstTransformer.CFGNode> visited = new HashSet<CfgToAstTransformer.CFGNode>();
    stack.Push(head);
    entry.successors.Add(head);
    head.predecessors.Add(entry);
    visited.Add(entry);
    while (stack.Count != 0) {
      var curr = stack.Pop();
      if (!visited.Contains(curr)) {
        visited.Add(curr);
        if (curr.successors.Count == 0) { //if no successors.
          curr.successors.Add(exit);
          exit.predecessors.Add(curr);
        }
        foreach (var succ in curr.successors) {
          succ.addPredecessor(curr);
          stack.Push(succ);
        }
      }
    }

    return visited;
  }

}