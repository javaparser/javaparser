package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class IfStatementContext extends StatementContext<IfStmt> {
//public class IfStatementContext extends AbstractJavaParserContext<IfStmt> {

    public IfStatementContext(IfStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }


    @Override
    public List<PatternExpr> patternExprsExposedToChild(Node child) {
        // If the given node is not within the "then" section, any PatternExpr variable is not within scope.
        // If the given node is not within the "condition", any PatternExpr variable is not within scope.
        boolean givenNodeIsWithinThenStatement = wrappedNode.getThenStmt().containsWithinRange(child);
        boolean givenNodeIsWithinCondition = wrappedNode.getCondition().containsWithinRange(child);
        if (!givenNodeIsWithinThenStatement && !givenNodeIsWithinCondition) {
            return Collections.emptyList();
        }

        List<PatternExpr> allPatternExprInCondition = wrappedNode.getCondition()
                .findAll(PatternExpr.class);

        // Filter to include only the pattern expressions that exist prior to the given node.
        return allPatternExprInCondition.stream()
                .filter(patternExpr -> patternExpr.getRange().get().end.isBefore(child.getRange().get().begin))
                .collect(Collectors.toList());
    }


    /**
     * <pre>{@code
     * if() {
     *     // Does not match here (doesn't need to, as stuff inside of the if() is likely in context..)
     * } else if() {
     *     // Matches here
     * } else {
     *     // Matches here
     * }
     * }</pre>
     *
     * @return true, If this is an if inside of an if...
     */
    public boolean nodeContextIsChainedIfElseIf(Context parentContext) {
        return parentContext instanceof AbstractJavaParserContext
                && ((AbstractJavaParserContext<?>) this).getWrappedNode() instanceof IfStmt
                && ((AbstractJavaParserContext<?>) parentContext).getWrappedNode() instanceof IfStmt;
    }

    /**
     * <pre>{@code
     * if() {
     *     // Does not match here (doesn't need to, as stuff inside of the if() is likely in context..)
     * } else {
     *     // Does not match here, as the else block is a field inside of an ifstmt as opposed to child
     * }
     * }</pre>
     *
     * @return true, If this is an else inside of an if...
     */
    public boolean nodeContextIsImmediateChildElse(Context parentContext) {
        if (!(parentContext instanceof AbstractJavaParserContext)) {
            return false;
        }
        if (!(this instanceof AbstractJavaParserContext)) {
            return false;
        }

        AbstractJavaParserContext<?> abstractContext = (AbstractJavaParserContext<?>) this;
        AbstractJavaParserContext<?> abstractParentContext = (AbstractJavaParserContext<?>) parentContext;

        Node wrappedNode = abstractContext.getWrappedNode();
        Node wrappedParentNode = abstractParentContext.getWrappedNode();

        if (wrappedParentNode instanceof IfStmt) {
            IfStmt parentIfStmt = (IfStmt) wrappedParentNode;
            if (parentIfStmt.getElseStmt().isPresent()) {
                boolean currentNodeIsAnElseBlock = parentIfStmt.getElseStmt().get() == wrappedNode;
                if (currentNodeIsAnElseBlock) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * <pre>{@code
     * if() {
     *     // Does not match here (doesn't need to, as stuff inside of the if() is likely in context..)
     * } else {
     *     // Does not match here, as the else block is a field inside of an ifstmt as opposed to child
     * }
     * }</pre>
     *
     * @return true, If this is an else inside of an if...
     */
    public boolean nodeContextIsThenOfIfStmt(Context parentContext) {
        if (!(parentContext instanceof AbstractJavaParserContext)) {
            return false;
        }
        if (!(this instanceof AbstractJavaParserContext)) {
            return false;
        }

        AbstractJavaParserContext<?> abstractContext = (AbstractJavaParserContext<?>) this;
        AbstractJavaParserContext<?> abstractParentContext = (AbstractJavaParserContext<?>) parentContext;

        Node wrappedNode = abstractContext.getWrappedNode();
        Node wrappedParentNode = abstractParentContext.getWrappedNode();

        if (wrappedParentNode instanceof IfStmt) {
            IfStmt parentIfStmt = (IfStmt) wrappedParentNode;
            boolean currentNodeIsAnElseBlock = parentIfStmt.getThenStmt() == wrappedNode;
            if (currentNodeIsAnElseBlock) {
                return true;
            }
        }

        return false;
    }


    public boolean nodeContextIsConditionOfIfStmt(Context parentContext) {
        if (!(parentContext instanceof AbstractJavaParserContext)) {
            return false;
        }
        if (!(this instanceof AbstractJavaParserContext)) {
            return false;
        }

        AbstractJavaParserContext<?> abstractContext = (AbstractJavaParserContext<?>) this;
        AbstractJavaParserContext<?> abstractParentContext = (AbstractJavaParserContext<?>) parentContext;

        Node wrappedNode = abstractContext.getWrappedNode();
        Node wrappedParentNode = abstractParentContext.getWrappedNode();

        if (wrappedParentNode instanceof IfStmt) {
            IfStmt parentIfStmt = (IfStmt) wrappedParentNode;
            boolean currentNodeIsCondition = parentIfStmt.getCondition() == wrappedNode;
            if (currentNodeIsCondition) {
                return true;
            }
        }

        return false;
    }
}
