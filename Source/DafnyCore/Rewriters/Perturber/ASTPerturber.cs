using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Perturber;

public class ASTPerturber {
  private static ISet<Expression> TransformLiteral(LiteralExpr literal) {
    var result = new HashSet<Expression>();
    if (literal.Value is bool b) {
      result.Add(new LiteralExpr(literal.tok, !b));
    } else if (literal.Value is BigInteger bi) {
      result.Add(new LiteralExpr(literal.tok, bi + 1));
      result.Add(new LiteralExpr(literal.tok, bi - 1));
    }

    return result;
  }

  //Expression Transformations

  private static ISet<Expression> TransformBinaryExpression(BinaryExpr expr) {
    var result = new HashSet<Expression>();
    var booleanOps = ImmutableHashSet.Create(
      BinaryExpr.Opcode.Iff,
      BinaryExpr.Opcode.Imp,
      BinaryExpr.Opcode.Exp,
      BinaryExpr.Opcode.And,
      BinaryExpr.Opcode.Or
    )
      ;
    var numericComparisonOps = ImmutableHashSet.Create(
      BinaryExpr.Opcode.Lt,
      BinaryExpr.Opcode.Le,
      BinaryExpr.Opcode.Ge,
      BinaryExpr.Opcode.Gt
    );
    var numericArithOps = ImmutableHashSet.Create(
      BinaryExpr.Opcode.Add,
      BinaryExpr.Opcode.Sub,
      BinaryExpr.Opcode.Mul,
      BinaryExpr.Opcode.Div
    );

    //Change op

    if (booleanOps.Contains(expr.Op)) {
      var toSwap = booleanOps.Remove(expr.Op).Add(BinaryExpr.Opcode.Eq).Add(BinaryExpr.Opcode.Neq);
      toSwap.ForEach(a => {
        result.Add(new BinaryExpr(expr.tok, a, expr.E0, expr.E1));
      });
    } else if (numericComparisonOps.Contains(expr.Op)) {
      var toSwap = numericComparisonOps.Remove(expr.Op).Add(BinaryExpr.Opcode.Eq).Add(BinaryExpr.Opcode.Neq);
      toSwap.ForEach(a => {
        result.Add(new BinaryExpr(expr.tok, a, expr.E0, expr.E1));
      });
    } else if (numericArithOps.Contains(expr.Op)) {
      var toSwap = numericArithOps.Remove(expr.Op);
      toSwap.ForEach(a => {
        result.Add(new BinaryExpr(expr.tok, a, expr.E0, expr.E1));
      });
    } else if (expr.Op is BinaryExpr.Opcode.Eq) {
      result.Add(new BinaryExpr(expr.tok, BinaryExpr.Opcode.Neq, expr.E0, expr.E1));
    } else if (expr.Op is BinaryExpr.Opcode.Neq) {
      result.Add(new BinaryExpr(expr.tok, BinaryExpr.Opcode.Eq, expr.E0, expr.E1));
    }
    //Transform each sub expression and then replace 
    var e0 = TransformExpression(expr.E0);
    foreach (var expr0 in e0) {
      result.Add(new BinaryExpr(expr.tok, expr.Op, expr0, expr.E1));
    }
    var e1 = TransformExpression(expr.E1);
    foreach (var expr1 in e1) {
      result.Add(new BinaryExpr(expr.tok, expr.Op, expr.E0, expr1));
    }
    return result;
  }

  private static HashSet<AssignmentRhs> TransformRhs(AssignmentRhs rhs) {
    var result = new HashSet<AssignmentRhs>();
    if (rhs is ExprRhs exprRhs) {
      var expressions = TransformExpression(exprRhs.Expr);
      expressions.ForEach(e => result.Add(new ExprRhs(e)));
    } else if (rhs is TypeRhs typeRhs) {

    }
    return result;
  }

  /**
   * Transforms an expression and returns a set of possible expressions.
   * The returned set of expressions should be their own object
   */
  private static ISet<Expression> TransformExpression(Expression expression) {
    var result = new HashSet<Expression>();
    if (expression is BinaryExpr b) {
      TransformBinaryExpression(b).ForEach(a => result.Add(a));
    } else if (expression is LiteralExpr l) {
      TransformLiteral(l).ForEach(a => result.Add(a));
    } else if (expression is ParensExpression p) {
      TransformExpression(p.ResolvedExpression).ForEach(e => result.Add(new ParensExpression(p.Tok, e)));
    }
    return result;
  }

  //Statement transformations
  private static ISet<Statement> TransformUpdateStatement(UpdateStmt assign) {
    var result = new HashSet<Statement>();
    assign.Rhss.Select((value, index) => new { value, index }).ForEach(
      rhs => {
        var transformed = TransformRhs(rhs.value);
        foreach (var transformRhs in transformed) {
          var updatedRhss = assign.Rhss.Select((value, index) => {
            if (index == rhs.index) {
              return transformRhs;
            } else {
              return value;
            }
          }).ToList();
          result.Add(new UpdateStmt(assign.RangeToken, assign.Lhss, updatedRhss));
        }
      });
    return result;
  }

  private static ISet<Statement> TransformVarDeclStatement(VarDeclStmt varDecl) {
    var result = new HashSet<Statement>();
    var transformedUpdates = TransformStatement(varDecl.Update);
    transformedUpdates.ForEach(a => {
      if (a is ConcreteUpdateStatement c) {
        result.Add(new VarDeclStmt(varDecl.RangeToken, varDecl.Locals, c));
      }
    }
    );
    return result;
  }

  private static ISet<Statement> TransformIfStmt(IfStmt ifStmt) {
    var result = new HashSet<Statement>();
    var transformedGuard = TransformExpression(ifStmt.Guard);
    var transformedTrueBranch = TransformStatement(ifStmt.Thn);
    var transformedElseBranch = TransformStatement(ifStmt.Els);
    transformedGuard.ForEach(g => result.Add(new IfStmt(ifStmt.RangeToken, ifStmt.IsBindingGuard, g, ifStmt.Thn, ifStmt.Els)));
    transformedTrueBranch.ForEach(g => result.Add(new IfStmt(ifStmt.RangeToken, ifStmt.IsBindingGuard, ifStmt.Guard, (BlockStmt)g, ifStmt.Els)));
    transformedElseBranch.ForEach(g => result.Add(new IfStmt(ifStmt.RangeToken, ifStmt.IsBindingGuard, ifStmt.Guard, ifStmt.Thn, g)));
    return result;
  }

  private static ISet<Statement> TransformWhileStmt(WhileStmt whileStmt) {
    var result = new HashSet<Statement>();
    var transformedGuard = TransformExpression(whileStmt.Guard);
    var transformedBody = TransformStatement(whileStmt.Body);
    transformedGuard.ForEach(g => result.Add(new WhileStmt(whileStmt.RangeToken, g, whileStmt.Invariants, whileStmt.Decreases, whileStmt.Mod, whileStmt.Body)));
    transformedBody.ForEach(g => result.Add(new WhileStmt(whileStmt.RangeToken, whileStmt.Guard, whileStmt.Invariants, whileStmt.Decreases, whileStmt.Mod, (BlockStmt)g)));
    return result;
  }

  private static ISet<Statement> TransformForLoopStmt(ForLoopStmt forLoopStmt) {
    var result = new HashSet<Statement>();
    var transformedStart = TransformExpression(forLoopStmt.Start);
    var transformedEnd = TransformExpression(forLoopStmt.End);
    var transformedBody = TransformStatement(forLoopStmt.Body);
    transformedStart.ForEach(g => result.Add(
      new ForLoopStmt(
        forLoopStmt.RangeToken,
        forLoopStmt.LoopIndex,
        g,
        forLoopStmt.End,
        forLoopStmt.GoingUp,
        forLoopStmt.Invariants,
        forLoopStmt.Decreases,
        forLoopStmt.Mod,
        forLoopStmt.Body,
        forLoopStmt.Attributes)));
    transformedEnd.ForEach(g => result.Add(
      new ForLoopStmt(
        forLoopStmt.RangeToken,
        forLoopStmt.LoopIndex,
        forLoopStmt.Start,
        g,
        forLoopStmt.GoingUp,
        forLoopStmt.Invariants,
        forLoopStmt.Decreases,
        forLoopStmt.Mod,
        forLoopStmt.Body,
        forLoopStmt.Attributes)));
    transformedBody.ForEach(g => result.Add(
      new ForLoopStmt(
        forLoopStmt.RangeToken,
        forLoopStmt.LoopIndex,
        forLoopStmt.Start,
        forLoopStmt.End,
        forLoopStmt.GoingUp,
        forLoopStmt.Invariants,
        forLoopStmt.Decreases,
        forLoopStmt.Mod,
        (BlockStmt)g,
        forLoopStmt.Attributes)));
    result.Add(
      new ForLoopStmt(
        forLoopStmt.RangeToken,
        forLoopStmt.LoopIndex,
        forLoopStmt.End,
        forLoopStmt.Start,
        !forLoopStmt.GoingUp,
        forLoopStmt.Invariants,
        forLoopStmt.Decreases,
        forLoopStmt.Mod,
        forLoopStmt.Body,
        forLoopStmt.Attributes));
    return result;
  }

  private static ISet<Statement> TransformBlockStmt(BlockStmt blockStmt) {
    var result = new HashSet<Statement>();
    //potential deletes allowed as well.
    blockStmt.Body.Select((value, index) => new { value, index })
      .ForEach(
        stmt => {
          var transformed = TransformStatement(stmt.value);
          foreach (var transformStmt in transformed) {
            var updatedBody = blockStmt.Body.Select((value, index) => {
              if (index == stmt.index) {
                return transformStmt;
              } else {
                return value;
              }
            }).ToList();
            result.Add(new BlockStmt(blockStmt.RangeToken, updatedBody));
          }
        }
      );
    return result;
  }


  private static ISet<Statement> TransformStatement(Statement stmt) {
    var result = new HashSet<Statement>();
    if (stmt is UpdateStmt update) {
      TransformUpdateStatement(update).ForEach(a => result.Add(a));
    } else if (stmt is VarDeclStmt varDecl) {
      TransformVarDeclStatement(varDecl).ForEach(a => result.Add(a));
    } else if (stmt is IfStmt ifStmt) {
      TransformIfStmt(ifStmt).ForEach(a => result.Add(a));
    } else if (stmt is WhileStmt whileStmt) {
      TransformWhileStmt(whileStmt).ForEach(a => result.Add(a));
    } else if (stmt is ForLoopStmt forLoopStmt) {
      TransformForLoopStmt(forLoopStmt).ForEach(a => result.Add(a));
    } else if (stmt is BlockStmt blockStmt) {
      TransformBlockStmt(blockStmt).ForEach(a => result.Add(a));
    }
    return result;
  }
}