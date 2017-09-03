package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.*;

import java.util.List;

/**
 * Consider Control Flow to determine which statements are reachable.
 *
 * Except for the special treatment of while, do, and for statements whose condition expression has the constant value
 * true, the values of expressions are not taken into account in the flow analysis.
 *
 * See JLS 14.21
 *
 * @author Federico Tomassetti
 */
public class ControlFlowLogic {

    private static ControlFlowLogic instance = new ControlFlowLogic();

    public static ControlFlowLogic getInstance() {
        return instance;
    }

    private ControlFlowLogic() {

    }

    /**
     * A break statement with no label attempts to transfer control to the innermost enclosing switch, while, do, or
     * for statement of the immediately enclosing method or initializer; this statement, which is called the break
     * target, then immediately completes normally.
     *
     *
     * A break statement with label Identifier attempts to transfer control to the enclosing labeled statement (§14.7)
     * that has the same Identifier as its label; this statement, which is called the break target, then immediately
     * completes normally. In this case, the break target need not be a switch, while, do, or for statement.
     */
    public Statement breakTarget(BreakStmt breakStmt) {
        throw new UnsupportedOperationException();
    }

    /**
     * A reachable break statement exits a statement if, within the break target, either there are no try statements
     * whose try blocks contain the break statement, or there are try statements whose try blocks contain the break
     * statement and all finally clauses of those try statements can complete normally.
     */
    public boolean exitTheStatement(BreakStmt breakStmt) {
        if (!isReachable(breakStmt)) {
            return false;
        }
        Statement breakTarget = breakTarget(breakStmt);
        for (TryStmt tryStmt : containedTryStmts(breakTarget)) {
            if (contains(tryStmt.getTryBlock(), breakStmt)) {
                if (!tryStmt.getFinallyBlock().isPresent() && !canCompleteNormally(tryStmt.getFinallyBlock().get())) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean continueADoStatement(ContinueStmt continueStmt, DoStmt doStmt) {
        for (TryStmt tryStmt : containedTryStmts(continueStmt)) {
            if (contains(tryStmt.getTryBlock(), continueStmt)) {
                if (!tryStmt.getFinallyBlock().isPresent() && !canCompleteNormally(tryStmt.getFinallyBlock().get())) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean contains(Statement container, Statement contained) {
        throw new UnsupportedOperationException();
    }

    private List<TryStmt> containedTryStmts(Statement statement) {
        throw new UnsupportedOperationException();
    }

    private <P extends Node> boolean parentIs(Node node, Class<P> parentClass) {
        if (node.getParentNode().isPresent()) {
            return parentClass.isInstance(node.getParentNode().get());
        } else {
            return false;
        }
    }

    // See JLS 14.21
    public boolean canCompleteNormally(Statement statement) {
        if (!isReachable(statement)) {
            return false;
        }
        if (statement instanceof BlockStmt) {
            BlockStmt blockStmt = (BlockStmt)statement;
            // An empty block that is not a switch block can complete normally iff it is reachable
            if (blockStmt.isEmpty() && !parentIs(statement, SwitchStmt.class)) {
                return isReachable(statement);
            }
            // A non-empty block that is not a switch block can complete normally iff the last statement in
            // it can complete normally.
            if (!blockStmt.isEmpty() && !parentIs(statement, SwitchStmt.class)) {
                return canCompleteNormally(blockStmt.getStatement(blockStmt.getStatements().size() - 1));
            }
        }
        throw new UnsupportedOperationException();
    }

    public boolean isReachable(Statement statement) {
        // The block that is the body of a constructor, method, instance initializer, or static initializer is
        // reachable.
        if (statement instanceof BlockStmt) {
            if (statement.getParentNode().isPresent()) {
                if (statement.getParentNode().get() instanceof ConstructorDeclaration) {
                    return true;
                }
                if (statement.getParentNode().get() instanceof MethodDeclaration) {
                    return true;
                }
                if (statement.getParentNode().get() instanceof InitializerDeclaration) {
                    return true;
                }
            }
        }
        // The first statement in a non-empty block that is not a switch block is reachable iff the block is reachable.

        // Every other statement S in a non-empty block that is not a switch block is reachable iff the statement
        // preceding S can complete normally.

        // FIXME
        throw new UnsupportedOperationException();
    }


}
