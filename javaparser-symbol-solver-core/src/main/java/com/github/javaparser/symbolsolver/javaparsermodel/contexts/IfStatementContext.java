package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.stmt.IfStmt;
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
}
