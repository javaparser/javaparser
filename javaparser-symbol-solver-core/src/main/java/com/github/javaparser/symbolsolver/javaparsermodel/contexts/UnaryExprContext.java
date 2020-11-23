package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;

public class UnaryExprContext extends AbstractJavaParserContext<UnaryExpr> {

    public UnaryExprContext(UnaryExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<PatternExpr> patternExprsExposedToDirectParent() {
        List<PatternExpr> results = new ArrayList<>();

        // Propagate any pattern expressions "up"
        if(wrappedNode.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
            Context innerContext = JavaParserFactory.getContext(wrappedNode.getExpression(), typeSolver);

            // Note that `UnaryExpr.Operator.LOGICAL_COMPLEMENT` is `!`
            // Previously negated pattern expressions are now now available (double negatives) -- e.g. if(!!("a" instanceof String s)) {}
            results.addAll(innerContext.negatedPatternExprsExposedToDirectParent());
        }

        return results;
    }

    @Override
    public List<PatternExpr> negatedPatternExprsExposedToDirectParent() {
        List<PatternExpr> results = new ArrayList<>();

        // Propagate any pattern expressions "up"
        if(wrappedNode.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
            Context innerContext = JavaParserFactory.getContext(wrappedNode.getExpression(), typeSolver);

            // Note that `UnaryExpr.Operator.LOGICAL_COMPLEMENT` is `!`
            // Previously available pattern expressions are now negated (double negatives) -- e.g. if(!("a" instanceof String s)) {}
            results.addAll(innerContext.patternExprsExposedToDirectParent());
        }

        return results;
    }

}
