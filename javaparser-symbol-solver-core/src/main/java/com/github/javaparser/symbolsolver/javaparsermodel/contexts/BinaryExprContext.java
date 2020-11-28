package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class BinaryExprContext extends AbstractJavaParserContext<BinaryExpr> {

    public BinaryExprContext(BinaryExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

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
    public List<PatternExpr> negatedPatternExprsExposedFromChildren() {

        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<PatternExpr> results = new ArrayList<>();

        // FIXME: Redo the `.getValue() == true` to take more complex code into account when determining if definitively true (e.g. `
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

            // TODO/FIXME: There are other cases where it may be ambiguously true until runtime e.g. `"x" instanceof String s == (new Random().nextBoolean())`

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

    private List<PatternExpr> patternExprsExposedToDirectParentFromBranch(Expression branch) {
        if (branch.isEnclosedExpr() || branch.isBinaryExpr() || branch.isUnaryExpr() || branch.isInstanceOfExpr()) {
            Context branchContext = JavaParserFactory.getContext(branch, typeSolver);
            return branchContext.patternExprsExposedFromChildren();
        }

        return new ArrayList<>();
    }

    private List<PatternExpr> negatedPatternExprsExposedToDirectParentFromBranch(Expression branch) {
        if (branch.isEnclosedExpr() || branch.isBinaryExpr() || branch.isUnaryExpr() || branch.isInstanceOfExpr()) {
            Context branchContext = JavaParserFactory.getContext(branch, typeSolver);
            return branchContext.negatedPatternExprsExposedFromChildren();
        }

        return new ArrayList<>();
    }

    public List<PatternExpr> patternExprsExposedToChild(Node child) {
        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<PatternExpr> results = new ArrayList<>();
        if (child == leftBranch) {
            results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
        } else if (child == rightBranch) {
            if (binaryExpr.getOperator().equals(BinaryExpr.Operator.AND)) {
                // "" instanceof String s && "" instanceof String s2
                results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
            }
        }
//        else if (binaryExpr.getOperator().equals(BinaryExpr.Operator.AND) && rightBranch.isAncestorOf(child)) {
//            // "" instanceof String s && "" instanceof String s2
//            results.addAll(patternExprsExposedToDirectParentFromBranch(leftBranch));
//        }

        return results;
    }


    public Optional<PatternExpr> patternExprInScope(String name) {
        BinaryExpr binaryExpr = wrappedNode;
        Expression leftBranch = binaryExpr.getLeft();
        Expression rightBranch = binaryExpr.getRight();

        List<PatternExpr> patternExprs = patternExprsExposedToDirectParentFromBranch(leftBranch);
        Optional<PatternExpr> localResolutionResults = patternExprs
                .stream()
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
        return parentContext.patternExprInScope(name);
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
