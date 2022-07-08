package com.github.javaparser.symbolsolver.javaparsermodel.contexts.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AbstractJavaParserContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JmlQuantifiedExprContext extends AbstractJavaParserContext<JmlQuantifiedExpr> {
    public JmlQuantifiedExprContext(JmlQuantifiedExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }


    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        return new ArrayList<>(wrappedNode.getVariables());
    }


    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Parameter variable : wrappedNode.getVariables()) {
            if (variable.getNameAsString().equals(name)) {
                return SymbolReference.solved(JavaParserSymbolDeclaration.parameter(variable, typeSolver));
            }
        }
        return super.solveSymbol(name);
    }
}
