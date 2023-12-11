using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;
using Microsoft.Dafny.Perturber;
using Microsoft.Dafny.Triggers;

namespace Microsoft.Dafny;

public class PerturbationRewriter : IRewriter {

  static ISet<string> existingProgs = new HashSet<string>();
  private static int counter = 0;

  public PerturbationRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }
  /**
   * Perturbs the module definition and then prints the result program to file. The program is mutably modified,
   * printed, and then changed back to the original input.
   */
  public static void TransformProgram(Program program, ModuleDefinition moduleDefinition) {
    var programPath = Path.GetFullPath(program.FullName); //read includes statements
    var fullDfyFile = File.ReadAllText(programPath);
    var includes = String.Join("\n", fullDfyFile.Split("\n").Where(s => s.Trim().StartsWith("include")));
    // Console.WriteLine(includes);
    // Console.WriteLine(programPath);
    // Console.WriteLine(program.DefaultModule.ModuleDef);
    var declarations = moduleDefinition.TopLevelDecls;
    foreach (var decl in declarations) {
      if (decl is TopLevelDeclWithMembers tld) {
        foreach (MemberDecl member in tld.Members) {
          if (member is Method method) {
            if (method.Body == null || method.Body.Body.Count == 0) {
              continue;
            }
            var originalBody = method.Body;
            var perturbed = ASTPerturber.TransformStatement(method.Body, method.Outs);
            var slicingVars = method.Ens.SelectMany(e => ProgramSlicer.GetAllVariables(e.E)).ToHashSet();
            perturbed.UnionWith(
              ASTPerturber.TransformBlockStatementWithSlicing(method.Body, slicingVars, method.Outs));
            // Console.WriteLine(perturbed.Count);
            foreach (var stmt in perturbed) {
              var dir = Path.GetDirectoryName(programPath);
              var fileName = "_" + Path.GetFileNameWithoutExtension(programPath) + $"_{counter}" + Path.GetExtension(programPath);
              var updatedFile = Path.Join(dir, fileName);
              // Console.WriteLine(updatedFile);
              var writer = new StreamWriter(updatedFile);
              //write includes
              var pr = new Printer(writer, program.Options,
                PrintModes.NoIncludes); // need to make the output writer her
              method.Body = (BlockStmt)stmt;
              pr.PrintProgram(program, true);
              writer.Close();
              var old = File.ReadAllText(updatedFile);
              if (existingProgs.Contains(old)) {
                //in this case we want to delte the file.
                File.Delete(updatedFile);
              } else {
                writer = new StreamWriter(updatedFile);
                writer.Write(includes + "\n" + old);
                counter += 1;
                writer.Close();
                existingProgs.Add(old);
              }
            }

            method.Body = originalBody;
          }
        }
      }
    }

  }


  /**
   * Method to remove any loop invariants. Keeping it here for now for future transformations.
   */
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

}