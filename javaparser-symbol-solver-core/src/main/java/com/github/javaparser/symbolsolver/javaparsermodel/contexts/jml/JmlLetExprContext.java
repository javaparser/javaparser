package com.github.javaparser.symbolsolver.javaparsermodel.contexts.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.jml.expr.JmlLetExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AbstractJavaParserContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JmlLetExprContext extends AbstractJavaParserContext<JmlLetExpr> {
    public JmlLetExprContext(JmlLetExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return new ArrayList<>(wrappedNode.getVariables().getVariables());
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (VariableDeclarator variable : wrappedNode.getVariables().getVariables()) {
            if (variable.getNameAsString().equals(name)) {
                return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(variable, typeSolver));
            }
        }
        return super.solveSymbol(name);
    }
}
