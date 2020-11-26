package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;


public class EnclosedExprContext extends AbstractJavaParserContext<EnclosedExpr> {

    public EnclosedExprContext(EnclosedExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<PatternExpr> patternExprsExposedFromChildren() {
        // Propagate any pattern expressions "up" without modification
        Context innerContext = JavaParserFactory.getContext(wrappedNode.getInner(), typeSolver);
        List<PatternExpr> results = new ArrayList<>(innerContext.patternExprsExposedFromChildren());

        return results;
    }

    @Override
    public List<PatternExpr> negatedPatternExprsExposedFromChildren() {
        // Propagate any pattern expressions "up" without modification
        Context innerContext = JavaParserFactory.getContext(wrappedNode.getInner(), typeSolver);
        List<PatternExpr> results = new ArrayList<>(innerContext.negatedPatternExprsExposedFromChildren());

        return results;
    }

}
