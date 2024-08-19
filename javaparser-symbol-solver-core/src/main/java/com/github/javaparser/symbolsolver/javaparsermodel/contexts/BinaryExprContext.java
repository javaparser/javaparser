/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableResult;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import java.util.*;

public class BinaryExprContext extends ExpressionContext<BinaryExpr> {

    public BinaryExprContext(BinaryExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<TypePatternExpr> typePatternExprsExposedFromChildren() {

        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<TypePatternExpr> results = new ArrayList<>();

        if (binaryExpr.getOperator().equals(BinaryExpr.Operator.EQUALS)) {
            if (rightBranch.isBooleanLiteralExpr()) {
                if (rightBranch.asBooleanLiteralExpr().getValue() == true) {
                    // "x" instanceof String s == true
                    results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
                } else {
                    // "x" instanceof String s == false
                }
            } else if (leftBranch.isBooleanLiteralExpr()) {
                if (leftBranch.asBooleanLiteralExpr().getValue() == true) {
                    // true == "x" instanceof String s
                    results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
                } else {
                    // false == "x" instanceof String s
                }
            }
        } else if (binaryExpr.getOperator().equals(BinaryExpr.Operator.NOT_EQUALS)) {
            if (rightBranch.isBooleanLiteralExpr()) {
                if (rightBranch.asBooleanLiteralExpr().getValue() == true) {
                    // "x" instanceof String s != true
                } else {
                    // "x" instanceof String s != false
                    results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
                }
            } else if (leftBranch.isBooleanLiteralExpr()) {
                if (leftBranch.asBooleanLiteralExpr().getValue() == true) {
                    // true != "x" instanceof String s
                } else {
                    // false != "x" instanceof String s
                    results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
                }
            }

            // TODO/FIXME: There are other cases where it may be ambiguously true until runtime e.g. `"x" instanceof
            // String s == (new Random().nextBoolean())`

        } else if (binaryExpr.getOperator().equals(BinaryExpr.Operator.AND)) {
            // "x" instanceof String s && s.length() > 0
            // "x" instanceof String s && "x" instanceof String s2
            results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
            results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
        } else {
            return new ArrayList<>();
        }

        return results;
    }

    @Override
    public List<TypePatternExpr> negatedTypePatternExprsExposedFromChildren() {

        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<TypePatternExpr> results = new ArrayList<>();

        // FIXME: Redo the `.getValue() == true` to take more complex code into account when determining if definitively
        // true (e.g. `
        if (binaryExpr.getOperator().equals(BinaryExpr.Operator.EQUALS)) {
            if (rightBranch.isBooleanLiteralExpr()) {
                if (isDefinitivelyTrue(rightBranch)) {
                    // "x" instanceof String s == true
                    // "x" instanceof String s == !(false)
                    // No negations.
                } else {
                    // "x" instanceof String s == false
                    // "x" instanceof String s == !(true)
                    results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
                }
            } else if (leftBranch.isBooleanLiteralExpr()) {
                if (isDefinitivelyTrue(leftBranch)) {
                    // true == "x" instanceof String s
                    // !(false) == "x" instanceof String s
                    // No negations.
                } else {
                    // false == "x" instanceof String s
                    // !(true) == "x" instanceof String s
                    results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
                }
            }
        } else if (binaryExpr.getOperator().equals(BinaryExpr.Operator.NOT_EQUALS)) {
            if (rightBranch.isBooleanLiteralExpr()) {
                if (isDefinitivelyTrue(rightBranch)) {
                    // "x" instanceof String s != true
                    // "x" instanceof String s != !(false)
                    results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
                } else {
                    // "x" instanceof String s != false
                    // "x" instanceof String s != !(true)
                }
            } else if (leftBranch.isBooleanLiteralExpr()) {
                if (isDefinitivelyTrue(leftBranch)) {
                    // true != "x" instanceof String s
                    // !(false) != "x" instanceof String s
                    results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
                } else {
                    // false != "x" instanceof String s
                    // !(true) != "x" instanceof String s
                }
            }

            // TODO/FIXME: There are other cases where it may be ambiguously true until runtime e.g. `"x" instanceof
            // String s == (new Random().nextBoolean())`

        } else if (binaryExpr.getOperator().equals(BinaryExpr.Operator.AND)) {
            // "x" instanceof String s && s.length() > 0
            // "x" instanceof String s && "x" instanceof String s2
            results.addAll(negatedPatternExprsExposedToDirectParentFromBranch(leftBranch));
            results.addAll(negatedPatternExprsExposedToDirectParentFromBranch(rightBranch));
        } else {
            return new ArrayList<>();
        }

        return results;
    }

    private List<TypePatternExpr> patternExprsExposedToDirectParentFromBranch(Expression branch) {
        if (branch.isEnclosedExpr() || branch.isBinaryExpr() || branch.isUnaryExpr() || branch.isInstanceOfExpr()) {
            Context branchContext = JavaParserFactory.getContext(branch, typeSolver);
            return branchContext.typePatternExprsExposedFromChildren();
        }

        return new ArrayList<>();
    }

    private List<TypePatternExpr> negatedPatternExprsExposedToDirectParentFromBranch(Expression branch) {
        if (branch.isEnclosedExpr() || branch.isBinaryExpr() || branch.isUnaryExpr() || branch.isInstanceOfExpr()) {
            Context branchContext = JavaParserFactory.getContext(branch, typeSolver);
            return branchContext.negatedTypePatternExprsExposedFromChildren();
        }

        return new ArrayList<>();
    }

    public List<TypePatternExpr> typePatternExprsExposedToChild(Node child) {
        if (wrappedNode.getOperator().equals(BinaryExpr.Operator.AND)) {
            return typePatternExprsExposedToChildByAnd(child);
        }
        if (wrappedNode.getOperator().equals(BinaryExpr.Operator.OR)) {
            return typePatternExprsExposedToChildByOr(child);
        }
        return Collections.emptyList();
    }

    /**
     * The following rules apply to a conditional-and expression a && b:
     * - A pattern variable introduced by a when true is definitely matched at b.
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.1.1
     */
    private List<TypePatternExpr> typePatternExprsExposedToChildByAnd(Node child) {
        if (!wrappedNode.getOperator().equals(BinaryExpr.Operator.AND)) {
            throw new IllegalStateException(
                    "Attempting to find patterns exposed by &&-expression, but wrapped operator is a "
                            + wrappedNode.getOperator().asString());
        }

        List<TypePatternExpr> results = new LinkedList<>();

        if (wrappedNode.getRight().containsWithinRange(child)) {
            PatternVariableVisitor variableVisitor = PatternVariableVisitor.getInstance();
            PatternVariableResult patternsInScope = wrappedNode.getLeft().accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfTrue());
        }

        return results;
    }

    /**
     * The following rules apply to a conditional-and expression a || b:
     * - A pattern variable introduced by a when false is definitely matched at b.
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.1.2
     */
    private List<TypePatternExpr> typePatternExprsExposedToChildByOr(Node child) {
        if (!wrappedNode.getOperator().equals(BinaryExpr.Operator.OR)) {
            throw new IllegalStateException(
                    "Attempting to find patterns exposed by ||-expression, but wrapped operator is a "
                            + wrappedNode.getOperator().asString());
        }

        List<TypePatternExpr> results = new LinkedList<>();

        if (wrappedNode.getRight().containsWithinRange(child)) {
            PatternVariableVisitor variableVisitor = PatternVariableVisitor.getInstance();
            PatternVariableResult patternsInScope = wrappedNode.getLeft().accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfFalse());
        }

        return results;
    }

    public Optional<TypePatternExpr> typePatternExprInScope(String name) {
        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<TypePatternExpr> patternExprs = patternExprsExposedToDirectParentFromBranch(leftBranch);
        Optional<TypePatternExpr> localResolutionResults = patternExprs.stream()
                .filter(vd -> vd.getNameAsString().equals(name))
                .findFirst();

        if (localResolutionResults.isPresent()) {
            return localResolutionResults;
        }

        // If we don't find the parameter locally, escalate up the scope hierarchy to see if it is declared there.
        if (!getParent().isPresent()) {
            return Optional.empty();
        }
        Context parentContext = getParent().get();
        return parentContext.typePatternExprInScope(name);
    }

    private boolean isDefinitivelyTrue(Expression expression) {
        // TODO: Consider combinations of literal true/false, enclosed expressions, and negations.
        if (expression.isBooleanLiteralExpr()) {
            if (expression.asBooleanLiteralExpr().getValue() == true) {
                return true;
            }
        }
        return false;
    }

    private boolean isDefinitivelyFalse(Expression expression) {
        // TODO: Consider combinations of literal true/false, enclosed expressions, and negations.
        if (expression.isBooleanLiteralExpr()) {
            if (expression.asBooleanLiteralExpr().getValue() == false) {
                return true;
            }
        }
        return false;
    }
}
