package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.List;
import java.util.Optional;

/**
 * @author Fred Lefévère-Laoide
 */
public class CatchClauseContext extends AbstractJavaParserContext<CatchClause> {

    public CatchClauseContext(CatchClause wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(wrappedNode.getParameter(), typeSolver);
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = AbstractJavaParserContext.solveWith(sb, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(wrappedNode.getParameter(), typeSolver);
        Optional<Value> symbolReference = solveWithAsValue(sb, name, typeSolver);
        if (symbolReference.isPresent()) {
            // Perform parameter type substitution as needed
            return symbolReference;
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly, TypeSolver typeSolver) {
        return getParent().solveMethod(name, argumentsTypes, false, typeSolver);
    }
}
