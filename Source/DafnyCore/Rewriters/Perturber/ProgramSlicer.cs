using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Perturber;

public class ProgramSlicer {

  public static Dictionary<CfgToAstTransformer.CFGNode, ISet<IVariable>> computeProgramSlice(ISet<CfgToAstTransformer.CFGNode> nodes, ISet<IVariable> initialVars, List<Formal> outs) {
    Console.WriteLine("Computing Program slice");
    initialVars.ForEach(v => Console.Write(v.Name + ",\n"));
    Dictionary<CfgToAstTransformer.CFGNode, ISet<IVariable>> result = new Dictionary<CfgToAstTransformer.CFGNode, ISet<IVariable>>();
    Queue<CfgToAstTransformer.CFGNode> worklist = new Queue<CfgToAstTransformer.CFGNode>();
    foreach (var node in nodes) {
      worklist.Enqueue(node);
      if (node is CfgToAstTransformer.ExitNode) {
        result.Add(node, initialVars);
      } else {
        result.Add(node, new HashSet<IVariable>());
      }
    }
    while (worklist.Count != 0) {
      var curr = worklist.Dequeue();
      var inputToCurr = new HashSet<IVariable>(); //this is the union of all the successors
      var isExitOrEntry = (curr is CfgToAstTransformer.EntryNode || curr is CfgToAstTransformer.ExitNode);
      ISet<IVariable> defined =
        isExitOrEntry ? new HashSet<IVariable>() : Defined(curr.getStmt(), outs);
      ISet<IVariable> used =
        isExitOrEntry ? new HashSet<IVariable>() : Used(curr.getStmt());
      curr.successors.ForEach(s => result[s].ForEach(v => inputToCurr.Add(v)));
      ISet<IVariable> firstComponent = new HashSet<IVariable>();
      inputToCurr.ForEach(v => {
        if (!defined.Contains(v)) {
          firstComponent.Add(v);
        }
      });
      ISet<IVariable> secondComponent = defined.Overlaps(inputToCurr) ? used : new HashSet<IVariable>();
      var old = new HashSet<IVariable>(result[curr]);

      result[curr].UnionWith(firstComponent);
      result[curr].UnionWith(secondComponent);

      if (!old.SetEquals(result[curr])) {
        curr.predecessors.ForEach(worklist.Enqueue);
      }
    }
    //Now that we have the initial, we need to return it along with the set of uhhh statements that are in the slice. 
    //Think about how we want to do this. Does it matter whether or not we keep the indirect? If we don't then our slices are worse, but 
    //that's fine as long as it's runnable and able to be verified. This just means that there will be more interesting control flow things that must be done. 
    //This essentially means that if we keep a statement that is inside a control flow, we should keep that statmenet along with the control flow. Easy enough. 
    return result;

  }

  public static HashSet<IVariable> Defined(Statement stmt, List<Formal> outs) {
    var result = new HashSet<IVariable>();
    if (stmt is ConcreteUpdateStatement c) { //need to add handling for method calls 
      c.Lhss.ForEach(e => {
        GetAllVariables(e).ForEach(i => result.Add(i));
      });
    } else if (stmt is VarDeclStmt v) {
      v.Locals.ForEach(local => result.Add(local));
    } else if (stmt is ReturnStmt) {
      outs.ForEach(f => result.Add(f));
    } else if (stmt is ForLoopStmt f) {
      result.Add(f.LoopIndex);
    } else {
      //TODO We should try to be sound here with respect to the heap, but for now it's fine

    }
    return result;
  }

  public static HashSet<IVariable> Used(Statement stmt) {
    HashSet<IVariable> result = new HashSet<IVariable>();
    //This is annoying because some rhs could have this right, like in sequence selects? Let's
    // just consider sequences selects to both use and define the variables. 
    if (stmt is ConcreteUpdateStatement c) {
      c.Lhss.ForEach(e => {
        if (!(e.Resolved is IdentifierExpr)) {
          GetAllVariables(e).ForEach(i => result.Add(i));
        }
      }); //this should add everything but normal var assingment which is good?
      //add rhs
      if (c is AssignOrReturnStmt ar) {
        ar.Rhss.ForEach(e => GetAllVariables(e).ForEach(i => result.Add(i)));
      } else if (c is UpdateStmt u) {
        u.Rhss.ForEach(e => GetAllVariables(e).ForEach(i => result.Add(i)));
      } else if (c is AssignSuchThatStmt a) {
        GetAllVariables(a.Expr).ForEach(i => result.Add(i));
      }

    } else if (stmt is VarDeclStmt v) {
      if (v.Update != null) {
        Used(v.Update).ForEach(ivar => result.Add(ivar)); //here all the LHS will be local variables. 
      }
    } else {
      stmt.SubExpressions.ForEach(se => GetAllVariables(se).ForEach(var => result.Add(var))); //this should get al uses
    }
    return result;
  }

  public static HashSet<IVariable> GetAllVariables(Expression expression) {
    var result = new HashSet<IVariable>();
    if (expression.Resolved is IdentifierExpr i) {
      result.Add(i.Var);
      return result;
    }
    var subExprs = expression.SubExpressions;
    foreach (var subExpr in subExprs) {
      GetAllVariables(subExpr).ForEach(g => result.Add(g));
    }
    return result;
  }

  public static HashSet<IVariable> GetAllVariables(AssignmentRhs assignmentRhs) {
    var result = new HashSet<IVariable>();
    assignmentRhs.SubExpressions.ForEach(se => GetAllVariables(se).ForEach(n => result.Add(n)));
    return result;
  }
}