package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * @author Fred Lefévère-Laoide
 */
public class CatchClauseContext extends AbstractJavaParserContext<CatchClause> {

    public CatchClauseContext(CatchClause wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(wrappedNode.getParameter(), typeSolver);
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = AbstractJavaParserContext.solveWith(sb, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name) {
        SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(wrappedNode.getParameter(), typeSolver);
        Optional<Value> symbolReference = solveWithAsValue(sb, name);
        if (symbolReference.isPresent()) {
            // Perform parameter type substitution as needed
            return symbolReference;
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name);
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return Collections.emptyList();
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        if (child == getWrappedNode().getBody()) {
            return Collections.singletonList(getWrappedNode().getParameter());
        }
        return Collections.emptyList();
    }
}
