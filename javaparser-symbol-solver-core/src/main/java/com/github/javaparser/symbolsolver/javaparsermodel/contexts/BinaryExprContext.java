package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class BinaryExprContext extends AbstractJavaParserContext<BinaryExpr> {

    public BinaryExprContext(BinaryExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    // TODO: Add in mechanism where any PatternExpr on the left branch becomes available within the right branch


    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        BinaryExpr binaryExpr = wrappedNode;

        // Not applicable for || -- Pattern will only be created and used on the right when instanceof evaluates to true
        if (binaryExpr.getOperator() == BinaryExpr.Operator.AND) {
            Expression leftBranch = binaryExpr.getLeft();
            List<PatternExpr> patternExprs = leftBranch.findAll(PatternExpr.class);
            for (PatternExpr patternExpr : patternExprs) {
                if (patternExpr.getName().getIdentifier().equals(name)) {
                    return SymbolReference.solved(JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver));
                }
            }
        }

        // If not solved here, continue searching...
        return solveSymbolInParentContext(name);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        BinaryExpr binaryExpr = wrappedNode;
        // FIXME: Consider negations...
        // FIXME: Consider child binary expressions...
        // FIXME: Do something with "variables available" methods...

        // Not applicable for || -- Pattern will only be created and used on the right when instanceof evaluates to true
        if (binaryExpr.getOperator() == BinaryExpr.Operator.EQUALS) {
            // Only consider the left branch -- patterns on the right hand side should never be available to the left branch.
            List<PatternExpr> patternExprs = binaryExpr.getLeft().findAll(PatternExpr.class);
            for (PatternExpr patternExpr : patternExprs) {
                if (patternExpr.getName().getIdentifier().equals(name)) {
                    JavaParserSymbolDeclaration decl = JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver);
                    return Optional.of(Value.from(decl));
                }
            }
        }

        if (binaryExpr.getOperator() == BinaryExpr.Operator.AND) {
            // FIXME: If the usage is in the right branch, is it defined in the right branch... etc...
            List<PatternExpr> patternExprs = binaryExpr.getLeft().findAll(PatternExpr.class);
            for (PatternExpr patternExpr : patternExprs) {
                if (patternExpr.getName().getIdentifier().equals(name)) {
                    JavaParserSymbolDeclaration decl = JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver);
                    return Optional.of(Value.from(decl));
                }
            }
        }

        // If there is no parent
        if(!getParent().isPresent()) {
            return Optional.empty();
        }
        Context parentContext = getParent().get();

        // if nothing is found we should ask the parent context
        return parentContext.solveSymbolAsValue(name);
    }


    /**
     * FIXME: This returns the patternExpr POTENTIALLY available to the child.
     */
    @Override
    public List<PatternExpr> patternExprsExposedToChild(Node child) {
        List<PatternExpr> res = new LinkedList<>();

        // PatternExpr will only be exposed to the given child IF it is in the right-hand branch of this binary expr.
        boolean givenNodeIsWithinRightBranch = wrappedNode.getRight().containsWithinRange(child);
        if (!givenNodeIsWithinRightBranch) {
            return res;
        }

        List<PatternExpr> allPatternExprInLeftBranch = wrappedNode.getLeft()
                .findAll(PatternExpr.class);

        // Filter to include only the pattern expressions that exist prior to the given node.
        return allPatternExprInLeftBranch.stream()
                .filter(patternExpr -> patternExpr.getRange().get().end.isBefore(child.getRange().get().begin))
                .collect(Collectors.toList());
    }


    @Override
    public List<PatternExpr> patternExprsExposedToDirectParent() {

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
    public List<PatternExpr> negatedPatternExprsExposedToDirectParent() {

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
            return leftBranchContext.patternExprsExposedToDirectParent();
        }

        return new ArrayList<>();
    }
}
