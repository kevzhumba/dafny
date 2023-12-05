using System;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Perturber;

public class CfgToAstTransformer {

  public static BlockStmt CfgToAstForNodeList(List<CFGNode> nodes, ISet<CFGNode> slice) {
    List<Statement> statements = new List<Statement>();
    foreach (var node in nodes) {
      if (slice.Contains(node)) {
        statements.Add(CfgToAstForStatement(node, slice));
      }
    }
    return new BlockStmt(RangeToken.NoToken, statements);
  }

  public static Statement CfgToAstForStatement(CFGNode cfgNode, ISet<CFGNode> slice) {
    if (cfgNode is IfNode i) {
      return CfgToAst(i, slice);
    }

    if (cfgNode is WhileNode w) {
      return CfgToAst(w, slice);
    }

    if (cfgNode is ForNode f) {
      return CfgToAst(f, slice);
    }
    //in this case, our node is a normal statement node. Just return the statement.
    return cfgNode.getStmt();
  }

  public static ForLoopStmt CfgToAst(ForNode forNode, ISet<CFGNode> slice) {
    return forNode.constructFromThis(CfgToAstForNodeList(forNode.body, slice));
  }

  public static WhileStmt CfgToAst(WhileNode whileNode, ISet<CFGNode> slice) {
    List<Statement> statements = new List<Statement>();
    foreach (var node in whileNode.body) {
      if (slice.Contains(node)) {
        statements.Add(CfgToAstForStatement(node, slice));
      }
    }

    return whileNode.constructFromThis(CfgToAstForNodeList(whileNode.body, slice));
  }

  public static IfStmt CfgToAst(IfNode ifNode, ISet<CFGNode> slice) {
    Console.WriteLine(ifNode);
    List<Statement> elseStatements = new List<Statement>();
    foreach (var elsNode in ifNode.els) {
      if (slice.Contains(elsNode)) {
        elseStatements.Add(CfgToAstForStatement(elsNode, slice));
      }
    }
    //do some processing for this, i.e. if else is empty just return null, otherwise if its an if statement do an if statement,
    //otherwise block statement
    var thnStatement = CfgToAstForNodeList(ifNode.thn, slice);
    var elsStatement = (elseStatements.Count == 0)
      ? null
      : ((elseStatements.Count > 1) ? new BlockStmt(RangeToken.NoToken, elseStatements) : elseStatements[0]);
    return ifNode.constructFromThis(thnStatement, elsStatement);
  }

  public static (CFGNode, ISet<CFGNode>, ISet<CFGNode>, List<CFGNode>) AstToCfgForStatement(Statement stmt) {
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
      return (node, new HashSet<CFGNode>(), new HashSet<CFGNode> { node }, new List<CFGNode> { node });
    } else {
      var endNodes = new HashSet<CFGNode>();
      var node = new NormalStmtNode(stmt);
      endNodes.Add(node);
      return (node, endNodes, new HashSet<CFGNode> { node }, new List<CFGNode> { node });
    }

  }

  /**
   * The ends of this is break statements or the ends of last statement in the block. Return statements should always be connected to the exit node
   */
  public static (CFGNode, ISet<CFGNode>, ISet<CFGNode>, List<CFGNode>) AstToCfg(BlockStmt blockStmt) {
    CFGNode head = null;
    var stmts = blockStmt.Body;
    ISet<CFGNode> previousEndNodes = new HashSet<CFGNode>();
    var endNodes = new HashSet<CFGNode>();
    var allNodes = new HashSet<CFGNode>();
    List<CFGNode> topLevelNodes = new List<CFGNode>();
    for (int i = 0; i < blockStmt.Body.Count; i++) {
      var currStmt = stmts[i];
      var (stmtHead, stmtEndNodes, nodes, stmtTopLevelNode) = AstToCfgForStatement(currStmt); //toplevelnode is a singleton
      topLevelNodes.AddRange(stmtTopLevelNode);
      if (i == 0) {
        head = stmtHead;
      }
      nodes.ForEach(a => allNodes.Add(a));

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
    return (head, endNodes, allNodes, topLevelNodes);
  }

  /**
   * The ends of this is the ends of each branch, unless its a return 
   */
  public static (CFGNode, ISet<CFGNode>, ISet<CFGNode>, List<CFGNode>) AstToCfg(IfStmt ifStmt) {
    var head = new IfNode(ifStmt);
    var resultEndNodes = new HashSet<CFGNode>();
    var allNodes = new HashSet<CFGNode> { head };
    var (thenHead, thenEndNodes, thenNodes, listTopLevelNodesThn) = AstToCfg(ifStmt.Thn);
    head.thn = listTopLevelNodesThn;
    head.addSuccessor(thenHead);
    thenEndNodes.ForEach(a => resultEndNodes.Add(a));
    thenNodes.ForEach(a => {
      allNodes.Add(a);
      a.parentBranchNodes.Add(head);
    });
    if (ifStmt.Els != null) {
      var (elseHead, elseEndNodes, elseNodes, listTopLevelNodesEls) = AstToCfgForStatement(ifStmt.Els);
      head.els = listTopLevelNodesEls;
      head.addSuccessor(elseHead);
      elseEndNodes.ForEach(a => resultEndNodes.Add(a));
      elseNodes.ForEach(a => {
        allNodes.Add(a);
        a.parentBranchNodes.Add(head);
      });
    } else {
      head.els = new List<CFGNode>();
      resultEndNodes.Add(head);
    }
    return (head, resultEndNodes, allNodes, new List<CFGNode> { head });
  }

  public static (CFGNode, ISet<CFGNode>, ISet<CFGNode>, List<CFGNode>) AstToCfg(WhileStmt whileStmt) {
    var head = new WhileNode(whileStmt);
    var allNodes = new HashSet<CFGNode> { head };
    var (bodyHead, bodyEndNodes, bodyNodes, listTopLevelNodes) = AstToCfg(whileStmt.Body); //body end nodes
    head.body = listTopLevelNodes;
    bodyNodes.ForEach(a => {
      allNodes.Add(a);
      a.parentBranchNodes.Add(head);
    });
    head.addSuccessor(bodyHead);
    var resultEndNodes = new HashSet<CFGNode>();
    resultEndNodes.Add(head);
    foreach (var node in bodyEndNodes) {
      if (node.getStmt() is BreakStmt b) {
        if (b.IsContinue) {
          node.addSuccessor(head);
        } else {
          resultEndNodes.Add(node); //break statement should be an end node 
        }
      } else {
        node.addSuccessor(head); //essentially, ends of body edge should go to the head
      }
    }

    return (head, resultEndNodes, allNodes, new List<CFGNode> { head });
  }


  public static (CFGNode, ISet<CFGNode>, ISet<CFGNode>, List<CFGNode>) AstToCfg(ForLoopStmt stmt) {
    var head = new ForNode(stmt);
    var allNodes = new HashSet<CFGNode> { head };
    var (bodyHead, bodyEndNodes, bodyNodes, listTopLevelNodes) = AstToCfg(stmt.Body);
    head.body = listTopLevelNodes;
    allNodes.UnionWith(bodyNodes);
    head.addSuccessor(bodyHead);
    bodyNodes.ForEach(a => {
      allNodes.Add(a);
      a.parentBranchNodes.Add(head);
    });
    var resultEndNodes = new HashSet<CFGNode>();
    resultEndNodes.Add(head);
    foreach (var node in bodyEndNodes) {
      if (node.getStmt() is BreakStmt b) {
        if (b.IsContinue) {
          node.addSuccessor(head);
        } else {
          resultEndNodes.Add(node); //break statement should be an end node 
        }
      } else {
        node.addSuccessor(head); //essentially, ends of body edge should go to the head
      }
    }
    return (head, resultEndNodes, allNodes, new List<CFGNode> { head });
  }


  public abstract class CFGNode {
    public IList<CFGNode> parentBranchNodes = new List<CFGNode>(); //first branches in the list are iner branches, last ones are outer
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

    public List<CFGNode> thn;
    public List<CFGNode> els;

    public IfNode(IfStmt stmt) {
      Stmt = new IfStmt(stmt.RangeToken, stmt.IsBindingGuard, stmt.Guard, null, null);
    }

    public override Statement getStmt() {
      return Stmt;
    }

    public override string ToString() {
      return "If(" + Stmt.Guard + ")";
    }

    public IfStmt constructFromThis(BlockStmt thn, Statement els) {
      return new IfStmt(Stmt.RangeToken, Stmt.IsBindingGuard, Stmt.Guard, thn, els);
    }
  }

  public class WhileNode : CFGNode {
    public readonly WhileStmt Stmt;

    public List<CFGNode> body;

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

    public WhileStmt constructFromThis(BlockStmt body) {
      return new WhileStmt(Stmt.RangeToken, Stmt.Guard, Stmt.Invariants, Stmt.Decreases, Stmt.Mod, body,
        Stmt.Attributes);
    }
  }

  public class ForNode : CFGNode {
    public readonly ForLoopStmt Stmt;

    public List<CFGNode> body;

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

    public ForLoopStmt constructFromThis(BlockStmt body) {
      return new ForLoopStmt(
        Stmt.RangeToken,
        Stmt.LoopIndex,
        Stmt.Start,
        Stmt.End,
        Stmt.GoingUp,
        Stmt.Invariants,
        Stmt.Decreases,
        Stmt.Mod,
        body,
        Stmt.Attributes);
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