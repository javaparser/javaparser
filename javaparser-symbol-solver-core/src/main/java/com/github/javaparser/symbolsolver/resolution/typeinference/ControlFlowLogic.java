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
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
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

    /**
     * Determines normal completion for reachable blocks, if statements, synchronized statements,
     * and simple statements. Unreachable statements cannot complete normally.
     *
     * This analysis is incomplete. In particular, normal completion of basic loops, try statements,
     * switches, and labeled statements is not implemented.
     *
     * @throws UnsupportedOperationException if reachability or normal completion requires an unsupported rule
     */
    public boolean canCompleteNormally(Statement statement) {
        if (!isReachable(statement)) {
            return false;
        }
        return canCompleteNormallyWhenReachable(statement);
    }

    private boolean canCompleteNormallyWhenReachable(Statement statement) {
        if (statement.isBlockStmt()) {
            for (Statement child : statement.asBlockStmt().getStatements()) {
                if (!canCompleteNormallyWhenReachable(child)) {
                    return false;
                }
            }
            return true;
        }
        if (statement.isIfStmt()) {
            IfStmt ifStmt = statement.asIfStmt();
            return !ifStmt.getElseStmt().isPresent()
                    || canCompleteNormallyWhenReachable(ifStmt.getThenStmt())
                    || canCompleteNormallyWhenReachable(ifStmt.getElseStmt().get());
        }
        if (statement.isSynchronizedStmt()) {
            return canCompleteNormallyWhenReachable(
                    statement.asSynchronizedStmt().getBody());
        }
        // Reuse the existing visitor only for statements whose current implementations
        // do not delegate recursively or contain unimplemented control-flow rules.
        // In particular, WhileStmt/DoStmt/ForStmt currently return true as a FIXME.
        if (statement.isEmptyStmt()
                || statement.isExpressionStmt()
                || statement.isAssertStmt()
                || statement.isLocalClassDeclarationStmt()
                || statement.isLocalRecordDeclarationStmt()
                || statement.isLocalEnumDeclarationStmt()
                || statement.isReturnStmt()
                || statement.isThrowStmt()
                || statement.isBreakStmt()
                || statement.isContinueStmt()
                || statement.isYieldStmt()
                || statement.isExplicitConstructorInvocationStmt()
                || statement.isForEachStmt()) {
            return statement.accept(new NormalCompletionVisitor(), null);
        }
        throw new UnsupportedOperationException("Normal completion is not implemented for "
                + statement.getClass().getSimpleName());
    }

    private boolean isReachableBecauseOfPosition(Statement statement) {
        Node parent = statement
                .getParentNode()
                .orElseThrow(
                        () -> new UnsupportedOperationException("Reachability requires an enclosing AST context for "
                                + statement.getClass().getSimpleName()));

        if (parent instanceof MethodDeclaration
                && ((MethodDeclaration) parent).getBody().orElse(null) == statement) {
            return true;
        }
        if (parent instanceof ConstructorDeclaration && ((ConstructorDeclaration) parent).getBody() == statement) {
            return true;
        }
        if (parent instanceof CompactConstructorDeclaration
                && ((CompactConstructorDeclaration) parent).getBody() == statement) {
            return true;
        }
        if (parent instanceof InitializerDeclaration && ((InitializerDeclaration) parent).getBody() == statement) {
            return true;
        }
        if (parent instanceof LambdaExpr && ((LambdaExpr) parent).getBody() == statement) {
            return true;
        }
        if (parent instanceof BlockStmt) {
            BlockStmt block = (BlockStmt) parent;
            boolean reachable = isReachable(block);
            for (Statement child : block.getStatements()) {
                if (child == statement) {
                    return reachable;
                }
                if (reachable) {
                    reachable = canCompleteNormallyWhenReachable(child);
                }
            }
            throw new IllegalStateException("Statement is not an immediate child of its block");
        }
        if (parent instanceof IfStmt || parent instanceof SynchronizedStmt || parent instanceof ForEachStmt) {
            return isReachable((Statement) parent);
        }
        // Loop conditions, catch reachability, labels, and switch-entry contexts
        // require additional JLS rules. Do not silently classify them as reachable.
        throw new UnsupportedOperationException(
                "Reachability is not implemented for " + statement.getClass().getSimpleName() + " under "
                        + parent.getClass().getSimpleName());
    }

    /**
     * Determines reachability from the statement's enclosing AST context and its position in a block.
     * Method, constructor, initializer, and lambda bodies are analysis entry points. Substatements of
     * if, synchronized, and enhanced for statements inherit their enclosing statement's reachability.
     *
     * @throws UnsupportedOperationException if the statement is detached or its enclosing context is unsupported
     */
    public boolean isReachable(Statement statement) {
        return isReachableBecauseOfPosition(statement);

        //
        //
        //
        //        A switch statement can complete normally iff at least one of the following is
        // true:
        // – The switch block is empty or contains only switch labels.
        // – The last statement in the switch block can complete normally.
        // – There is at least one switch label after the last switch block statement group. – The switch block does not
        // contain a default label.
        // – There is a reachable break statement that exits the switch statement.
        //        BLOCKS AND STATEMENTS Unreachable Statements 14.21
        //
        // A switch block is reachable iff its switch statement is reachable.
        //
        //        A statement in a switch block is reachable iff its switch statement is reachable
        // and at least one of the following is true:
        // – It bears a case or default label.
        // – There is a statement preceding it in the switch block and that preceding statement can complete normally.
        //
        // A while statement can complete normally iff at least one of the following is true:
        // – Thewhilestatementisreachableandtheconditionexpressionisnotaconstant
        // expression (§15.28) with value true.
        // – There is a reachable break statement that exits the while statement.
        //        The contained statement is reachable iff the while statement is reachable and the condition expression
        // is not a constant expression whose value is false.
        //
        //        A do statement can complete normally iff at least one of the following is true:
        // – The contained statement can complete normally and the condition expression
        // is not a constant expression (§15.28) with value true.
        // – The do statement contains a reachable continue statement with no label, and the do statement is the
        // innermost while, do, or for statement that contains that continue statement, and the continue statement
        // continues that do statement, and the condition expression is not a constant expression with value true.
        // – The do statement contains a reachable continue statement with a label L, and the do statement has label L,
        // and the continue statement continues that do statement, and the condition expression is not a constant
        // expression with value true.
        // – There is a reachable break statement that exits the do statement.
        //        The contained statement is reachable iff the do statement is reachable.
        //
        //        A basic for statement can complete normally iff at least one of the following
        // is true:
        // – The for statement is reachable, there is a condition expression, and the
        // condition expression is not a constant expression (§15.28) with value true.
        // – There is a reachable break statement that exits the for statement.
        //        The contained statement is reachable iff the for statement is reachable and the condition expression
        // is not a constant expression whose value is false.
        //
        // • An enhanced for statement can complete normally iff it is reachable.
        //
        // • A break, continue, return, or throw statement cannot complete normally.
        //
        // • A synchronized statement can complete normally iff the contained statement can complete normally.
        //        The contained statement is reachable iff the synchronized statement is reachable.
        //
        // • A try statement can complete normally iff both of the following are true:
        // – The try block can complete normally or any catch block can complete
        // normally.
        // – Ifthetrystatementhasafinallyblock,thenthefinallyblockcancomplete normally.
        //
        // • The try block is reachable iff the try statement is reachable.
        //
        // • A catch block C is reachable iff both of the following are true:
        // – Either the type of C's parameter is an unchecked exception type or Exception or a superclass of Exception,
        // or some expression or throw statement in the try block is reachable and can throw a checked exception whose
        // type is assignable to the type of C's parameter. (An expression is reachable iff the innermost statement
        // containing it is reachable.)
        // See §15.6 for normal and abrupt completion of expressions.
        // – There is no earlier catch block A in the try statement such that the type of C's
        // parameter is the same as or a subclass of the type of A's parameter.
        // • The Block of a catch block is reachable iff the catch block is reachable.
        // • If a finally block is present, it is reachable iff the try statement is reachable.
        //        One might expect the if statement to be handled in the following manner:
        // • An if-then statement can complete normally iff at least one of the following is true:
        // – The if-then statement is reachable and the condition expression is not a constant expression whose value is
        // true.
        // – The then-statement can complete normally.
        //        The then-statement is reachable iff the if-then statement is reachable and the
        // condition expression is not a constant expression whose value is false.
        // • An if-then-else statement can complete normally iff the then-statement can complete normally or the
        // else-statement can complete normally.
        //        BLOCKS AND STATEMENTS Unreachable Statements 14.21
        // The then-statement is reachable iff the if-then-else statement is reachable and the condition expression is
        // not a constant expression whose value is false.
        //        The else-statement is reachable iff the if-then-else statement is reachable and the condition
        // expression is not a constant expression whose value is true.
        //        This approach would be consistent with the treatment of other control structures. However, in order to
        // allow the if statement to be used conveniently for "conditional compilation" purposes, the actual rules
        // differ.

        // FIXME
        // throw new UnsupportedOperationException();
    }
}
