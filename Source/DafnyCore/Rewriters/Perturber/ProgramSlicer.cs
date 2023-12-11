using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Policy;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Perturber;

public class ProgramSlicer {


  /**
   * Algorithm to compute the program slice with respect to some set of variables and relevant node.
   * Algorithm taken from Weiser, basic worklist algorithm.
   */
  public static Dictionary<String, ISet<CfgToAstTransformer.CFGNode>> computeProgramSlice(
    ISet<CfgToAstTransformer.CFGNode> nodes, ISet<String> initialVars, List<Formal> outs, CfgToAstTransformer.CFGNode startingNode) {
    Dictionary<String, ISet<CfgToAstTransformer.CFGNode>> resultDict =
      new Dictionary<String, ISet<CfgToAstTransformer.CFGNode>>();
    foreach (var sliceVar in initialVars) {
      var (result, slice) = computeDirectlyDependentSlice(nodes, new HashSet<String> { sliceVar }, outs, startingNode);
      var changed = true;
      while (changed) {
        changed = false;
        var branchStatements = slice.SelectMany(a => a.parentBranchNodes).ToHashSet();
        foreach (var branch in branchStatements) {
          var used = Used(branch.getStmt());
          var (branchDirectDependent, addedStatements) = computeDirectlyDependentSlice(nodes, used, outs, branch);
          foreach (var kv in branchDirectDependent) {
            result[kv.Key].UnionWith(kv.Value);
          }
        }
        var newSlice = branchStatements.Union(result.Keys.Where(a => {
          var def = Defined(a, outs);
          return a.successors.Any(s => result[s].Overlaps(def));
        })).ToHashSet();
        if (!slice.SetEquals(newSlice)) {
          changed = true;
          slice = newSlice;
        }
      }
      //after this, slice contains the total 
      resultDict[sliceVar] = slice;
    }
    return resultDict;
  }


  /**
   * Computes directly dependent statements. Does not take into account dependencies based on control flow.
   */
  public static (Dictionary<CfgToAstTransformer.CFGNode, ISet<String>>, ISet<CfgToAstTransformer.CFGNode>) computeDirectlyDependentSlice(
    ISet<CfgToAstTransformer.CFGNode> nodes, ISet<String> initialVars, List<Formal> outs, CfgToAstTransformer.CFGNode startingNode) {
    Dictionary<CfgToAstTransformer.CFGNode, ISet<String>> result = new Dictionary<CfgToAstTransformer.CFGNode, ISet<String>>();
    Queue<CfgToAstTransformer.CFGNode> worklist = new Queue<CfgToAstTransformer.CFGNode>();
    ISet<CfgToAstTransformer.CFGNode> sliced = new HashSet<CfgToAstTransformer.CFGNode>();
    foreach (var node in nodes) {
      worklist.Enqueue(node);
      if (node == startingNode) {
        result.Add(node, initialVars);
      } else {
        result.Add(node, new HashSet<String>());
      }
    }
    while (worklist.Count != 0) {
      var curr = worklist.Dequeue();
      var inputToCurr = new HashSet<String>(); //this is the union of all the successors
      var isExitOrEntry = (curr is CfgToAstTransformer.EntryNode || curr is CfgToAstTransformer.ExitNode);
      ISet<String> defined =
        isExitOrEntry ? new HashSet<String>() : Defined(curr, outs);
      ISet<String> used =
        isExitOrEntry ? new HashSet<String>() : Used(curr.getStmt());
      curr.successors.ForEach(s => result[s].ForEach(v => inputToCurr.Add(v)));
      ISet<String> firstComponent = new HashSet<String>();
      inputToCurr.ForEach(v => {
        if (!defined.Contains(v)) {
          firstComponent.Add(v);
        }
      });
      ISet<String> secondComponent = defined.Overlaps(inputToCurr) ? used : new HashSet<String>();
      var old = new HashSet<String>(result[curr]);

      result[curr].UnionWith(firstComponent);
      result[curr].UnionWith(secondComponent);

      if (!old.SetEquals(result[curr])) {
        curr.predecessors.ForEach(worklist.Enqueue);
      }

      if (defined.Overlaps(inputToCurr)) { //add the node
        sliced.Add(curr);
      }
    }
    //Now that we have the initial, we need to return it along with the set of uhhh statements that are in the slice. 
    //Think about how we want to do this. Does it matter whether or not we keep the indirect? If we don't then our slices are worse, but 
    //that's fine as long as it's runnable and able to be verified. This just means that there will be more interesting control flow things that must be done. 
    //This essentially means that if we keep a statement that is inside a control flow, we should keep that statmenet along with the control flow. Easy enough. 
    return (result, sliced);
  }

  private static HashSet<String> GetAllDefinedVariables(ExtendedPattern ex) {
    var result = new HashSet<String>();
    if (ex is IdPattern i) {
      if (i.BoundVar != null) {
        result.Add(i.BoundVar.Name);
      } else if (i.Arguments != null) {
        i.Arguments.ForEach(arg => result.UnionWith(GetAllDefinedVariables(arg)));
      }
    }
    return result;
  }

  /*
   * Gets all defined variables for a node. Return statements define the
   * out variables. This is an underapproximation of the defined variables, as
   * procedure calls can define/change variables.
  */
  public static HashSet<String> Defined(CfgToAstTransformer.CFGNode node, List<Formal> outs) {
    var result = new HashSet<String>();
    if (node is CfgToAstTransformer.CaseNode caseNode) {
      return GetAllDefinedVariables(caseNode.CaseStmt.Pat);
    }
    var stmt = node.getStmt();
    if (stmt is ConcreteUpdateStatement c) { //need to add handling for method calls 
      c.Lhss.ForEach(e => {
        result.UnionWith(GetAllVariables(e));
      });
    } else if (stmt is VarDeclStmt v) {
      v.Locals.ForEach(local => result.Add(local.Name));
    } else if (stmt is ReturnStmt) {
      outs.ForEach(f => result.Add(f.Name));
    } else if (stmt is ForLoopStmt f) {
      result.Add(f.LoopIndex.Name);
    } else {
      //TODO We should try to be sound here with respect to the heap, but for now it's fine

    }
    return result;
  }

  /**
   * The variables that a statement uses.
   */
  public static HashSet<String> Used(Statement stmt) { //this relies on the fact that for the control flow we set the ast nodes to null
    HashSet<String> result = new HashSet<String>();
    if (stmt == null) {
      return result;
    }
    //This is annoying because some rhs could have this right, like in sequence selects? Let's
    // just consider sequences selects to both use and define the variables. This is technicaly correct
    if (stmt is ConcreteUpdateStatement c) {
      c.Lhss.ForEach(e => {
        if (!(e is NameSegment)) {
          result.UnionWith(GetAllVariables(e));
        }
      }); //this should add everything but normal var assingment which is good?
      //add rhs
      if (c is AssignOrReturnStmt ar) {
        ar.Rhss.ForEach(e => result.UnionWith(GetAllVariables(e)));
      } else if (c is UpdateStmt u) {
        u.Rhss.ForEach(e => result.UnionWith(GetAllVariables(e)));
      } else if (c is AssignSuchThatStmt a) {
        result.UnionWith(GetAllVariables(a.Expr));
      }

    } else if (stmt is VarDeclStmt v) {
      if (v.Update != null) {
        result.UnionWith(Used(v.Update));
      }
    } else {
      stmt.SubExpressions.ForEach(se => result.UnionWith(GetAllVariables(se))); //this should get al uses
    }
    return result;
  }

  /**
   * Gets all variables in an expression
   */
  public static HashSet<String> GetAllVariables(Expression expression) {
    var result = new HashSet<String>();
    if (expression is NameSegment n) {
      result.Add(n.Name);
      return result;
    }
    var subExprs = expression.SubExpressions;
    foreach (var subExpr in subExprs) {
      result.UnionWith(GetAllVariables(subExpr));
    }
    return result;
  }

  public static HashSet<String> GetAllVariables(AssignmentRhs assignmentRhs) {
    var result = new HashSet<String>();
    assignmentRhs.SubExpressions.ForEach(se => GetAllVariables(se).ForEach(n => result.Add(n)));
    return result;
  }



}