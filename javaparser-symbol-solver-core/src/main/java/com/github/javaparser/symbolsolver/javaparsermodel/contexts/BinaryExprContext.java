package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class BinaryExprContext extends AbstractJavaParserContext<BinaryExpr> {

    public BinaryExprContext(BinaryExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    // TODO: Add in mechanism where any PatternExpr on the left branch becomes available within the right branch


    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        List<PatternExpr> patternExprs = patternExprsExposedFromChildren();

        // Filter to include only the pattern expressions that exist prior to the given node.
        // FIXME: Consider the shared parent between the given nodes -- may be affected by negations.
        List<PatternExpr> matches = patternExprs.stream()
                .filter(patternExpr -> patternExpr.getNameAsString().equals(name))
                .collect(Collectors.toList());

        if(matches.size() == 1) {
            return SymbolReference.solved(JavaParserSymbolDeclaration.patternVar(matches.get(0), typeSolver));
        } else if(matches.size() > 1) {
            throw new IllegalStateException("Too many matches -- unclear how to solve.");
        } else {
            // if nothing is found we should ask the parent context
            return solveSymbolInParentContext(name);
        }
    }
//
//
//    /**
//     * FIXME: This returns the patternExpr POTENTIALLY available to the child.
//     */
//    @Override
//    public List<PatternExpr> patternExprsExposedToChild(Node child) {
//        List<PatternExpr> res = new LinkedList<>();
//
//
//        // PatternExpr will only be exposed to the given child IF it is in the right-hand branch of this binary expr.
//        boolean givenNodeIsWithinRightBranch = wrappedNode.getRight().containsWithinRange(child);
//        if (!givenNodeIsWithinRightBranch) {
//            return res;
//        }
//
//        // PatternExpr only propagates across and AND relationship..? TODO: Confirm/verify.
//        if(!wrappedNode.getOperator().equals(BinaryExpr.Operator.AND)) {
//            return res;
//        }
//
//        List<PatternExpr> patternExprs = patternExprsExposedToDirectParent();
//        List<PatternExpr> negatedPatternExprs = negatedPatternExprsExposedToDirectParent();
//
//        // Filter to include only the pattern expressions that exist prior to the given node.
//        // FIXME: Consider the shared parent between the given nodes -- may be affected by negations.
//        return patternExprs.stream()
//                .filter(patternExpr -> patternExpr.getRange().get().end.isBefore(child.getRange().get().begin))
//                .collect(Collectors.toList());
//    }


    @Override
    public List<PatternExpr> patternExprsExposedFromChildren() {

        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<PatternExpr> results = new ArrayList<>();

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

            // TODO/FIXME: There are other cases where it may be ambiguously true until runtime e.g. `"x" instanceof String s == (new Random().nextBoolean())`

        } else {
            return new ArrayList<>();
        }

        return results;
    }

    @Override
    public List<PatternExpr> negatedPatternExprsExposedFromChildren() {

        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<PatternExpr> results = new ArrayList<>();

        if (binaryExpr.getOperator().equals(BinaryExpr.Operator.EQUALS)) {
            if (rightBranch.isBooleanLiteralExpr()) {
                if (rightBranch.asBooleanLiteralExpr().getValue() == true) {
                    // "x" instanceof String s == true
                } else {
                    // "x" instanceof String s == false
                    results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
                }
            } else if (leftBranch.isBooleanLiteralExpr()) {
                if (leftBranch.asBooleanLiteralExpr().getValue() == true) {
                    // true == "x" instanceof String s
                } else {
                    // false == "x" instanceof String s
                    results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
                }
            }
        } else if (binaryExpr.getOperator().equals(BinaryExpr.Operator.NOT_EQUALS)) {
            if (rightBranch.isBooleanLiteralExpr()) {
                if (rightBranch.asBooleanLiteralExpr().getValue() == true) {
                    // "x" instanceof String s != true
                    results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
                } else {
                    // "x" instanceof String s != false
                }
            } else if (leftBranch.isBooleanLiteralExpr()) {
                if (leftBranch.asBooleanLiteralExpr().getValue() == true) {
                    // true != "x" instanceof String s
                    results.addAll(patternExprsExposedToDirectParentFromBranch(rightBranch));
                } else {
                    // false != "x" instanceof String s
                }
            }

            // TODO/FIXME: There are other cases where it may be ambiguously true until runtime e.g. `"x" instanceof String s == (new Random().nextBoolean())`

        } else {
            return new ArrayList<>();
        }

        return results;
    }

    private List<PatternExpr> patternExprsExposedToDirectParentFromBranch(Expression branch) {
        if (branch.isEnclosedExpr() || branch.isBinaryExpr() || branch.isUnaryExpr() || branch.isInstanceOfExpr()) {
            Context leftBranchContext = JavaParserFactory.getContext(branch, typeSolver);
            return leftBranchContext.patternExprsExposedFromChildren();
        }

        return new ArrayList<>();
    }
}
