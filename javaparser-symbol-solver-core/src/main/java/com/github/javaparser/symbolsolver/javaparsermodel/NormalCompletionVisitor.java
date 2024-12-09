/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.GenericVisitorWithDefaults;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.List;
import java.util.Optional;

/**
 * When deciding into which scope pattern variables should be introduced, it is sometimes necessary to determine whether
 * a statement can complete normally {@see https://docs.oracle.com/javase/specs/jls/se22/html/jls-14.html#jls-14.22}.
 * The JLS specifies that a statement can complete normally only if it is reachable and specifies rules for what it
 * means for a statement to be reachable, but that part can be ignored in JavaParser since having unreachable code
 * results in a compilation error and is thus not supported. This means that all of the rules are implemented with the
 * assumption that provided nodes are reachable.
 *
 * An example of where this is needed is for the following rule regarding pattern variables introduced by if-statements.
 * 6.3.2.2. if Statements {@see https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.2}:
 *   The following rules apply to a statement if (e) S (§14.9.1):
 *     A pattern variable is introduced by if (e) S iff (i) it is introduced by e when false and (ii) S cannot complete
 *     normally.
 *
 * This means that in this example:
 * {@code
 *   if (!(x instanceof Foo f)) {
 *       return;
 *   }
 *   System.out.println(f);
 * }
 * f will be in scope for the println call since the block making up the then-block of the if statement (S in the rule
 * above) cannot complete normally (since the last statement, return, cannot complete normally).
 * But, in this example:
 * {@code
 *   if (!(x instanceof Foo f)) { }
 * }
 * f is not introduced by the if statement since the empty then-block can complete normally.
 */
public class NormalCompletionVisitor extends GenericVisitorWithDefaults<Boolean, Void> {

    private static String[] nonEnhancedSwitchTypes = new String[] {
        "java.lang.Byte", "java.lang.Character", "java.lang.Integer", "java.lang.Short", "java.lang.String"
    };

    @Override
    public Boolean defaultAction(Node n, Void unused) {
        return true;
    }

    /**
     * A break statement cannot complete normally.
     */
    @Override
    public Boolean visit(BreakStmt breakStmt, Void unused) {
        return false;
    }

    /**
     * A continue statement cannot complete normally.
     */
    @Override
    public Boolean visit(ContinueStmt continueStmt, Void unused) {
        return false;
    }

    /**
     * A return statement cannot complete normally.
     */
    @Override
    public Boolean visit(ReturnStmt returnStmt, Void unused) {
        return false;
    }

    /**
     * A throw statement cannot complete normally.
     */
    @Override
    public Boolean visit(ThrowStmt throwStmt, Void unused) {
        return false;
    }

    /**
     * A yield statement cannot complete normally.
     */
    @Override
    public Boolean visit(YieldStmt yieldStmt, Void unused) {
        return false;
    }

    /**
     * An empty block that is not a switch block can complete normally iff it is reachable.
     *
     * A non-empty block that is not a switch block can complete normally iff the last statement in it can complete
     * normally.
     *
     * The first statement in a non-empty block that is not a switch block is reachable iff the block is reachable.
     *
     * Every other statement S in a non-empty block that is not a switch block is reachable iff the statement preceding
     * S can complete normally.
     */
    @Override
    public Boolean visit(BlockStmt block, Void unused) {
        return block.getStatements().isEmpty()
                || block.getStatements().getOLast().get().accept(this, unused);
    }

    /**
     * A labeled statement can complete normally if at least one of the following is true:
     * - The contained statement can complete normally.
     * - There is a reachable break statement that exits the labeled statement.
     */
    @Override
    public Boolean visit(LabeledStmt labeledStmt, Void unused) {
        if (labeledStmt.getStatement().accept(this, unused)) {
            return true;
        }

        List<BreakStmt> matchingBreaks = labeledStmt.findAll(
                BreakStmt.class,
                breakStmt -> breakStmt.getLabel().isPresent()
                        && breakStmt
                                .getLabel()
                                .get()
                                .getIdentifier()
                                .equals(labeledStmt.getLabel().getIdentifier()));

        return !matchingBreaks.isEmpty();
    }

    /**
     * An if-then statement can complete normally iff it is reachable.
     *
     * An if-then-else statement can complete normally iff the then-statement can complete normally or the
     * else-statement can complete normally.
     */
    @Override
    public Boolean visit(IfStmt ifStmt, Void unused) {
        if (!ifStmt.getElseStmt().isPresent()) {
            return true;
        }

        return ifStmt.getThenStmt().accept(this, unused)
                || ifStmt.getElseStmt().get().accept(this, unused);
    }

    /**
     * A while statement can complete normally iff at least one of the following is true:
     * - The while statement is reachable and the condition expression is not a constant expression with value true.
     * - There is a reachable break statement that exits the while statement.
     */
    @Override
    public Boolean visit(WhileStmt whileStmt, Void unused) {
        /**
         * FIXME: To implement this properly, constant expression evaluation would need to be implemented.
         *  this is specifically necessary for the first statement in the docstring.
         *
         * Simply returning true here will only cause issues where the while statement is the only statement, or the
         * last statement in a block for which it should be determined if it completes normally. For example, keeping
         * in mind the rule:
         *   A pattern variable is introduced by if (e) S iff
         *     (i) it is introduced by e when false and
         *     (ii) S cannot complete normally.
         *
         * {@code
         * while(true) {}
         * }
         * cannot complete normally since
         *   (i) the condition is a constant expression with value true and
         *   (ii) there is no break statement that exits the loop.
         *
         * Therefore, in:
         * {@code
         * if (!(x instanceof Foo f)) {
         *     while (true) {}
         * }
         * System.out.println(f);
         * }
         * the if statement should introduce the variable f into scope, so the f that is printed should be the pattern
         * variable.
         *
         * Simply returning true in this visit method would mean that {@code while (true) {}} is erroneously considered
         * to complete normally and this example will not be handled correctly.
         *
         * As long as the last statement is not the while, however, JavaParser will still handle this correctly for
         * compiling code.
         */
        return true;
    }

    /**
     * A do statement can complete normally iff at least one of the following is true:
     * - The contained statement can complete normally and the condition expression is not a constant expression
     *   with value true.
     * - The do statement contains a reachable continue statement with no label, and the do statement is the innermost
     *   while, do, or for statement that contains that continue statement, and the continue statement continues that do
     *   statement, and the condition expression is not a constant expression with value true.
     * - The do statement contains a reachable continue statement with label L, and the do statement has label L, and
     *   the continue statement continues that do statement, and the condition expression is not a constant expression
     *   with value true.
     * - There is a reachable break statement that exits the do statement.
     */
    @Override
    public Boolean visit(DoStmt doStmt, Void unused) {
        // FIXME: See comment in while visit method
        return true;
    }

    /**
     * A basic for statement can complete normally iff at least one of the following is true:
     * - The for statement is reachable, there is a condition expression, and the condition expression is not a constant
     *   expression with value true.
     * - There is a reachable break statement that exits the for statement.
     */
    @Override
    public Boolean visit(ForStmt forStmt, Void unused) {
        // FIXME: See comment in while visit method
        return true;
    }

    /**
     * A synchronized statement can complete normally iff the contained statement can complete normally.
     */
    @Override
    public Boolean visit(SynchronizedStmt synchronizedStmt, Void unused) {
        return synchronizedStmt.getBody().accept(this, unused);
    }

    /**
     * A try statement can complete normally iff both of the following are true:
     * - The try block can complete normally or any catch block can complete normally.
     * - If the try statement has a finally block, then the finally block can complete normally.
     */
    @Override
    public Boolean visit(TryStmt tryStmt, Void unused) {
        if (tryStmt.getFinallyBlock().isPresent() && !(tryStmt.getFinallyBlock().get()).accept(this, unused)) {
            return false;
        }

        if (tryStmt.getTryBlock().accept(this, unused)) {
            return true;
        }

        return tryStmt.getCatchClauses().stream()
                .anyMatch(catchClause -> catchClause.getBody().accept(this, unused));
    }

    /**
     * A switch statement whose switch block is empty, or contains only switch labels, can complete normally.
     *
     * A switch statement whose switch block consists of switch labeled statement groups can complete normally iff at
     *   least one of the following is true:
     * - The last statement in the switch block can complete normally.
     * - There is at least one switch label after the last switch block statement group.
     * - There is a reachable break statement that exits the switch statement.
     * - The switch statement is not enhanced and its switch block does not contain a default label.
     *
     * A switch statement whose switch block consists of switch rules can complete normally iff at least one of the
     *   following is true:
     * - One of the switch rules introduces a switch rule expression (which is necessarily a statement expression).
     * - One of the switch rules introduces a switch rule block that can complete normally.
     * - One of the switch rules introduces a switch rule block that contains a reachable break statement which exits
     *   the switch statement.
     * - The switch statement is not enhanced and its switch block does not contain a default label.
     */
    @Override
    public Boolean visit(SwitchStmt switchStmt, Void unused) {
        // TODO
        NodeList<SwitchEntry> entries = switchStmt.getEntries();

        if (entries.isEmpty()) {
            return true;
        }

        if (entries.get(0).getType().equals(SwitchEntry.Type.STATEMENT_GROUP)) {
            // In this case, the switch stmt is a classic switch, so check:
            // - The last statement in the switch block can complete normally.
            // - There is at least one switch label after the last switch block statement group.
            SwitchEntry lastEntry = entries.getOLast().get();
            if (lastEntry.getStatements().isEmpty()) {
                return true;
            }

            Statement lastStmt = lastEntry.getStatements().getOLast().get();
            if (lastStmt.accept(this, unused)) {
                return true;
            }
        } else if (entries.stream().anyMatch(entry -> switchRuleCompletesNormally(entry, unused))) {
            return true;
        }

        if (containsCorrespondingBreak(switchStmt)) {
            return true;
        }

        if (!isEnhanced(switchStmt) && !entries.stream().anyMatch(entry -> entry.isDefault())) {
            return true;
        }

        return false;
    }

    /**
     * A switch statement whose switch block consists of switch rules can complete normally iff at least one of the
     *   following is true:
     * - One of the switch rules introduces a switch rule expression (which is necessarily a statement
     *   expression).
     * - One of the switch rules introduces a switch rule block that can complete normally.
     */
    private boolean switchRuleCompletesNormally(SwitchEntry switchEntry, Void unused) {
        if (switchEntry.getType().equals(SwitchEntry.Type.EXPRESSION)) {
            return true;
        }

        if (switchEntry.getStatements().getOLast().isPresent()
                && switchEntry.getStatements().getOLast().get().accept(this, unused)) {
            return true;
        }

        return false;
    }

    /**
     * @param statement should be one of: SwitchStatement, WhileStatement, DoStatement, ForStatement
     * @return true if a break corresponding to the statement is found; false otherwise
     */
    public static boolean containsCorrespondingBreak(Statement statement) {
        List<BreakStmt> breakStatements = statement.findAll(
                BreakStmt.class, breakStmt -> !breakStmt.getLabel().isPresent());

        for (BreakStmt breakStmt : breakStatements) {
            Optional<Node> maybeParentNode = breakStmt.getParentNode();
            while (true) {
                if (!maybeParentNode.isPresent()) {
                    throw new IllegalStateException("Found AST node without a parent in subtree of Statement");
                }

                Node parentNode = maybeParentNode.get();

                if (parentNode instanceof SwitchStmt
                        || parentNode instanceof WhileStmt
                        || parentNode instanceof DoStmt
                        || parentNode instanceof ForStmt
                        || parentNode instanceof ForEachStmt) {
                    if (parentNode == statement) {
                        return true;
                    } else {
                        break;
                    }
                }

                maybeParentNode = maybeParentNode.flatMap(node -> node.getParentNode());
            }
        }

        return false;
    }

    /**
     * From https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.11.2
     *   An enhanced switch statement is one where either
     *   (i) the type of the selector expression is not char, byte, short, int, Character, Byte, Short, Integer, String,
     *       or an enum type, or
     *   (ii) there is a case pattern or null literal associated with the switch block.
     *
     * Since this relies on resolving the type of the selector expression, it might not be possible to determine whether
     * a given switch statement is enhanced or not. If this cannot be determined, assume that it is enhanced.
     */
    private static boolean isEnhanced(SwitchStmt stmt) {
        for (SwitchEntry entry : stmt.getEntries()) {
            if (entry.isDefault() || entry.getLabels().stream().anyMatch(label -> label.isNullLiteralExpr())) {
                return false;
            }
        }

        try {
            ResolvedType selectorType = stmt.getSelector().calculateResolvedType();

            if (selectorType.isPrimitive()) {
                return false;
            }

            for (String nonEnhancedTypeName : nonEnhancedSwitchTypes) {
                if (nonEnhancedTypeName.equals(selectorType.describe())) {
                    return false;
                }
            }

            if (selectorType.isReferenceType()) {
                ResolvedReferenceType selectorRefType = selectorType.asReferenceType();

                if (selectorRefType.getTypeDeclaration().isPresent()
                        && selectorRefType.getTypeDeclaration().get().isEnum()) {
                    return false;
                }
            }
        } catch (UnsolvedSymbolException e) {
            // Assume the switch is enhanced if the selector type cannot be resolved.
            return true;
        }

        return true;
    }
}
