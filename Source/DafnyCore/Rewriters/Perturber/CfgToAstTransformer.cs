using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Perturber;

public class CfgToAstTransformer {

  public static (CFGNode, ISet<CFGNode>) AstToCfgForStatement(Statement stmt) {
    if (stmt is BlockStmt b) {
      return AstToCfg(b);
    } else if (stmt is IfStmt i) {
      return AstToCfg(i);
    } else if (stmt is WhileStmt w) {
      return AstToCfg(w);
    } else if (stmt is ForLoopStmt f) {
      return AstToCfg(f);
    } else if (stmt is ReturnStmt r) {
      var node = new NormalStmtNode(stmt);
      return (node, new HashSet<CFGNode>());
    } else {
      var endNodes = new HashSet<CFGNode>();
      var node = new NormalStmtNode(stmt);
      endNodes.Add(node);
      return (node, endNodes);
    }

  }

  /**
   * The ends of this is break statements or the ends of last statement in the block. Return statements should always be connected to the exit node
   */
  public static (CFGNode, ISet<CFGNode>) AstToCfg(BlockStmt blockStmt) {
    CFGNode head = null;
    var stmts = blockStmt.Body;
    ISet<CFGNode> previousEndNodes = new HashSet<CFGNode>();
    var endNodes = new HashSet<CFGNode>();
    for (int i = 0; i < blockStmt.Body.Count; i++) {
      var currStmt = stmts[i];
      var (stmtHead, stmtEndNodes) = AstToCfgForStatement(currStmt);
      if (i == 0) {
        head = stmtHead;
      }

      foreach (var endNode in previousEndNodes) {
        endNode.addSuccessor(stmtHead);
      }

      previousEndNodes = stmtEndNodes;
      if (currStmt is BreakStmt) {
        endNodes.Add(stmtHead);
        previousEndNodes = new HashSet<CFGNode>();
      }
    }
    previousEndNodes.ForEach(a => endNodes.Add(a));
    return (head, endNodes);
  }

  /**
   * The ends of this is the ends of each branch, unless its a return 
   */
  public static (CFGNode, ISet<CFGNode>) AstToCfg(IfStmt ifStmt) {
    var head = new IfNode(ifStmt);
    var resultEndNodes = new HashSet<CFGNode>();
    var (thenHead, thenEndNodes) = AstToCfg(ifStmt.Thn);
    head.addSuccessor(thenHead);
    thenEndNodes.ForEach(a => resultEndNodes.Add(a));

    if (ifStmt.Els != null) {
      var (elseHead, elseEndNodes) = AstToCfgForStatement(ifStmt.Els);
      head.addSuccessor(elseHead);
      elseEndNodes.ForEach(a => resultEndNodes.Add(a));
    } else {
      resultEndNodes.Add(head);
    }
    return (head, resultEndNodes);
  }



  public static (CFGNode, ISet<CFGNode>) AstToCfg(WhileStmt whileStmt) {
    var head = new WhileNode(whileStmt);
    var (bodyHead, bodyEndNodes) = AstToCfg(whileStmt.Body); //body end nodes
    head.addSuccessor(bodyHead);
    var resultEndNodes = new HashSet<CFGNode>();
    resultEndNodes.Add(head);
    foreach (var node in bodyEndNodes) {
      if (node is NormalStmtNode n) {
        if (n.Stmt is BreakStmt b) {
          if (b.IsContinue) {
            node.addSuccessor(head);
          } else {
            resultEndNodes.Add(node); //break statement should be an end node
          }
        }
      } else {
        node.addSuccessor(head); //essentially, ends of body edge should go to the head
      }
    }

    return (head, resultEndNodes);
  }


  public static (CFGNode, ISet<CFGNode>) AstToCfg(ForLoopStmt stmt) {
    var head = new ForNode(stmt);
    var (bodyHead, bodyEndNodes) = AstToCfg(stmt.Body);
    head.addSuccessor(bodyHead);
    var resultEndNodes = new HashSet<CFGNode>();
    resultEndNodes.Add(head);
    foreach (var node in bodyEndNodes) {
      if (node is NormalStmtNode n) {
        if (n.Stmt is BreakStmt b) {
          if (b.IsContinue) {
            node.addSuccessor(head);
          } else {
            resultEndNodes.Add(node); //break statement should be an end node
          }
        }
      } else {
        node.addSuccessor(head); //essentially, ends of body edge should go to the head
      }
    }
    return (head, resultEndNodes);
  }


  public abstract class CFGNode {
    public ISet<CFGNode> successors = new HashSet<CFGNode>();
    public ISet<CFGNode> predecessors = new HashSet<CFGNode>();

    public void addPredecessor(CFGNode node) {
      predecessors.Add(node);

    }

    public void addSuccessor(CFGNode node) {
      successors.Add(node);
    }

    public abstract Statement getStmt();
  }

  public class IfNode : CFGNode {
    public readonly IfStmt Stmt;

    public IfNode(IfStmt stmt) {
      Stmt = new IfStmt(stmt.RangeToken, stmt.IsBindingGuard, stmt.Guard, null, null);
    }

    public override Statement getStmt() {
      return Stmt;
    }

    public override string ToString() {
      return "If(" + Stmt.Guard + ")";
    }
  }

  public class WhileNode : CFGNode {
    public readonly WhileStmt Stmt;

    public WhileNode(WhileStmt stmt) {
      Stmt = new WhileStmt(stmt.RangeToken, stmt.Guard, stmt.Invariants, stmt.Decreases, stmt.Mod, null,
        stmt.Attributes);
    }
    public override Statement getStmt() {
      return Stmt;
    }
    public override string ToString() {
      return "While(" + Stmt.Guard + ")";
    }
  }

  public class ForNode : CFGNode {
    public readonly ForLoopStmt Stmt;

    public ForNode(ForLoopStmt stmt) {
      Stmt = new ForLoopStmt(
        stmt.RangeToken,
        stmt.LoopIndex,
        stmt.Start,
        stmt.End,
        stmt.GoingUp,
        stmt.Invariants,
        stmt.Decreases,
        stmt.Mod,
        null,
        stmt.Attributes);
    }
    public override Statement getStmt() {
      return Stmt;
    }
    public override string ToString() {
      return "For(" + Stmt.LoopIndex + ", " + Stmt.Start + ", " + Stmt.End + ")";
    }

  }

  public class NormalStmtNode : CFGNode {
    public readonly Statement Stmt;

    public NormalStmtNode(Statement stmt) {
      Stmt = stmt;
    }
    public override Statement getStmt() {
      return Stmt;
    }

    public override string ToString() {
      return "NormalStmt(" + Stmt + ")";
    }
  }

  public class EntryNode : CFGNode {
    public override Statement getStmt() {
      return null;
    }

    public override string ToString() {
      return "Entry";
    }
  }

  public class ExitNode : CFGNode {
    public override Statement getStmt() {
      return null;
    }

    public override string ToString() {
      return "Exit";
    }
  }
}