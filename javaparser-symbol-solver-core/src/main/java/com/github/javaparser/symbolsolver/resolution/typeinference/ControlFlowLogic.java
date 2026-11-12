/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.symbolsolver.javaparsermodel.NormalCompletionVisitor;
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

    private ControlFlowLogic() {}

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
                if (!tryStmt.getFinallyBlock().isPresent()
                        && !canCompleteNormally(tryStmt.getFinallyBlock().get())) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean continueADoStatement(ContinueStmt continueStmt, DoStmt doStmt) {
        for (TryStmt tryStmt : containedTryStmts(continueStmt)) {
            if (contains(tryStmt.getTryBlock(), continueStmt)) {
                if (!tryStmt.getFinallyBlock().isPresent()
                        && !canCompleteNormally(tryStmt.getFinallyBlock().get())) {
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

    // See JLS 14.21
    public boolean canCompleteNormally(Statement statement) {
        if (!isReachable(statement)) {
            return false;
        }

        return statement.accept(new NormalCompletionVisitor(), null);
    }

    /**
     * Reachability is decided by the position of a node in the AST (JLS 14.22), so this walks up the parents instead of
     * dispatching on the kind of the statement itself.
     *
     * Constant expression evaluation is not available, so contexts whose reachability depends on it (the body of a
     * while or basic for statement) and contexts that require exception analysis (catch blocks) are reported with an
     * {@link UnsupportedOperationException} instead of being guessed.
     */
    public boolean isReachable(Statement statement) {
        return isReachableNode(statement);
    }

    private boolean isReachableNode(Node node) {
        Node parent = node.getParentNode()
                .orElseThrow(() -> new UnsupportedOperationException(
                        "Cannot determine reachability without an enclosing AST context for "
                                + node.getClass().getSimpleName()));

        // The block that is the body of a constructor, method, instance initializer, or static initializer is
        // reachable. The same holds for the body of a lambda and of a switch expression.
        if (parent instanceof CallableDeclaration
                || parent instanceof CompactConstructorDeclaration
                || parent instanceof InitializerDeclaration
                || parent instanceof LambdaExpr
                || parent instanceof SwitchExpr) {
            return true;
        }

        // The first statement in a non-empty block that is not a switch block is reachable iff the block is reachable.
        // Every other statement S in a non-empty block that is not a switch block is reachable iff the statement
        // preceding S can complete normally.
        if (parent instanceof BlockStmt) {
            return precedingStatementsCompleteNormally(((BlockStmt) parent).getStatements(), node)
                    && isReachableNode(parent);
        }

        // A statement in a switch block is reachable iff its switch statement is reachable and it bears a case or
        // default label, or the statement preceding it can complete normally.
        if (parent instanceof SwitchEntry) {
            return precedingStatementsCompleteNormally(((SwitchEntry) parent).getStatements(), node)
                    && isReachableNode(parent);
        }

        // These are reachable iff the enclosing node is reachable:
        // - the contained statement of a labeled, synchronized, do and enhanced for statement
        // - the then and else statements of an if statement (the condition is deliberately ignored, JLS 14.22)
        // - the try block and the finally block of a try statement
        // - a switch entry, which is reachable iff its switch is reachable
        if (parent instanceof LabeledStmt
                || parent instanceof SynchronizedStmt
                || parent instanceof IfStmt
                || parent instanceof DoStmt
                || parent instanceof ForEachStmt
                || parent instanceof TryStmt
                || parent instanceof SwitchStmt) {
            return isReachableNode(parent);
        }

        throw new UnsupportedOperationException("Cannot determine reachability of "
                + node.getClass().getSimpleName() + " under "
                + parent.getClass().getSimpleName());
    }

    /**
     * @return false if a statement before {@code node} (compared by identity) cannot complete normally. Statements
     * before it are known to be reachable, as otherwise an earlier one would already have been rejected.
     */
    private boolean precedingStatementsCompleteNormally(List<Statement> siblings, Node node) {
        for (Statement sibling : siblings) {
            if (sibling == node) {
                return true;
            }
            if (!sibling.accept(new NormalCompletionVisitor(), null)) {
                return false;
            }
        }
        return true;
    }
}
