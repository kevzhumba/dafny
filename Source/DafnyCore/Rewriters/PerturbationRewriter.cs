using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;
using Microsoft.Dafny.Perturber;
using Microsoft.Dafny.Triggers;

namespace Microsoft.Dafny;

public class PerturbationRewriter : IRewriter {


  public PerturbationRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    var declarations = moduleDefinition.TopLevelDecls;
    foreach (var decl in declarations) {
      if (decl is TopLevelDeclWithMembers tld) {
        foreach (MemberDecl member in tld.Members) {
          if (member is Method method) {
            ProgramDependenceSlicing(method);
            var (head, ends, allNodes, toplevelNodes) = CfgToAstTransformer.AstToCfgForStatement(method.Body);
            CfgToAstTransformer.CFGNode entry = new CfgToAstTransformer.EntryNode();
            CfgToAstTransformer.CFGNode exit = new CfgToAstTransformer.ExitNode();
            var nodes = CfgUtil.DFS(head, entry, exit);
            TransformMethod(method);
          }
        }
      }
    }
  }

  private void TransformMethod(Method method) {
    RemoveInvariants(method);
  }

  private void RemoveInvariants(Method method) {
    var block = method.Body.Body;
    var result = new List<Statement>();
    foreach (var stmt in block) {
      // Console.WriteLine(stmt);
      // Console.WriteLine(stmt.GetType());
      if (stmt is WhileStmt w) {
        result.Add(new WhileStmt(w.RangeToken, w.Guard, new List<AttributedExpression>(), w.Decreases, w.Mod, w.Body));
      } else if (stmt is ForLoopStmt f1) {
        result.Add(new ForLoopStmt(f1.RangeToken,
          f1.LoopIndex,
          f1.Start,
          f1.End,
          f1.GoingUp,
          new List<AttributedExpression>(),
          f1.Decreases,
          f1.Mod,
          f1.Body,
          f1.Attributes));
      } else {
        result.Add(stmt);
      }
    }
    method.Body = new BlockStmt(method.Body.RangeToken, result);
  }

  //Program Slicing Functionality
  private static void ProgramDependenceSlicing(Method method) {
    var postConds = method.Ens;
    var varsInPostconds = new HashSet<IVariable>();
    foreach (var postCond in postConds) {
      var variablesInPostCond = ProgramSlicer.GetAllVariables(postCond.E);
      variablesInPostCond.ForEach(a => varsInPostconds.Add(a));
      // Console.WriteLine(expression);
    }
    var (head, endNodes, _, topLevelNodes) = CfgToAstTransformer.AstToCfgForStatement(method.Body);
    var exit = new CfgToAstTransformer.ExitNode();
    var entry = new CfgToAstTransformer.EntryNode();
    endNodes.ForEach(a => a.addSuccessor(exit));
    var nodes = CfgUtil.DFS(head, entry, exit);
    CfgUtil.PrintDotGraph(nodes);
    var slicesForVar = ProgramSlicer.computeProgramSlice(nodes, varsInPostconds, method.Outs, exit);

    Console.WriteLine("Slicing");
    foreach (var kv in slicesForVar) {
      Console.WriteLine(kv.Key.Name);
      kv.Value.ForEach(Console.WriteLine);
      Console.WriteLine(CfgToAstTransformer.CfgToAstForNodeList(topLevelNodes, kv.Value));
    }
  }
}