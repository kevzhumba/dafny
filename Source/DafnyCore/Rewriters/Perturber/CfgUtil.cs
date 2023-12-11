using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.Perturber;

public class CfgUtil {

  /**
   * Visits every node starting at the head of the graph, filling in any missing predecessor and successor information
   */
  public static ISet<CfgToAstTransformer.CFGNode> DFS(CfgToAstTransformer.CFGNode head, CfgToAstTransformer.CFGNode entry, CfgToAstTransformer.CFGNode exit) {
    Stack<CfgToAstTransformer.CFGNode> stack = new Stack<CfgToAstTransformer.CFGNode>();
    ISet<CfgToAstTransformer.CFGNode> visited = new HashSet<CfgToAstTransformer.CFGNode>();
    stack.Push(head);
    entry.successors.Add(head);
    head.predecessors.Add(entry);
    visited.Add(entry);
    visited.Add(exit);
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

  /**
   * Prints a dot representation of the control flow graph.
   */
  public static void PrintDotGraph(ISet<CfgToAstTransformer.CFGNode> nodes) {
    Dictionary<CfgToAstTransformer.CFGNode, int> map = new Dictionary<CfgToAstTransformer.CFGNode, int>();
    Console.WriteLine("digraph G {");
    var count = 0;
    foreach (var node in nodes) {
      map[node] = count;
      Console.WriteLine($"n_{count++}[label=\"{node}\"]");
    }

    foreach (var node in nodes) {
      foreach (var succ in node.successors) {
        Console.WriteLine($"n_{map[node]} -> n_{map[succ]}");
      }
    }

    Console.WriteLine("}");
  }
}