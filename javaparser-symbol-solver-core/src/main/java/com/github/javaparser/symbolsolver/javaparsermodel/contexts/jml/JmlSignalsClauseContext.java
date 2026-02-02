package com.github.javaparser.symbolsolver.javaparsermodel.contexts.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AbstractJavaParserContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JmlSignalsClauseContext extends AbstractJavaParserContext<JmlSignalsClause> {
    public JmlSignalsClauseContext(JmlSignalsClause wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        return Collections.singletonList(wrappedNode.getParameter());
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        if (wrappedNode.getParameter().getNameAsString().equals(name)) {
            return SymbolReference.solved(
                    JavaParserSymbolDeclaration.parameter(wrappedNode.getParameter(), typeSolver));
        }
        return super.solveSymbol(name);
    }
}
