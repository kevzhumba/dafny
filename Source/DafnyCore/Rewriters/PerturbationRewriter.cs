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
            var (head, ends) = CfgToAstTransformer.AstToCfgForStatement(method.Body);
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

    var (head, _) = CfgToAstTransformer.AstToCfgForStatement(method.Body);
    var nodes = CfgUtil.DFS(head, new CfgToAstTransformer.EntryNode(), new CfgToAstTransformer.ExitNode());

    foreach (var variable in varsInPostconds) {
      var slice = ProgramSlicer.computeProgramSlice(nodes, new HashSet<IVariable> { variable }, method.Outs);
      slice.ForEach(pv => {
        Console.WriteLine(pv.Key);
        pv.Value.ForEach(v => Console.Write(v.Name + ", "));
        Console.WriteLine("\n");
      });
    }
  }



















}