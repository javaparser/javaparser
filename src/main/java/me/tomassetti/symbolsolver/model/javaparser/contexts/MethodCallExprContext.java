package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.expr.MethodCallExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

import java.util.List;

/**
 * Created by federico on 31/07/15.
 */
public class MethodCallExprContext extends AbstractJavaParserContext<MethodCallExpr> {

    public MethodCallExprContext(MethodCallExpr wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope() != null) {
            // TODO resolve the scope and get a context from there
            SymbolReference<SymbolDeclaration> declScope = new JavaParserFacade(typeSolver).solve(wrappedNode.getScope());
            if (declScope.isSolved()) {
                TypeDeclaration typeOfDeclScope = declScope.getCorrespondingDeclaration().getType();
                return typeOfDeclScope.getContext().solveMethod(name, parameterTypes, typeSolver);
            } else {
                // TODO this should be improved to indicate that is the scope that has not been solved
                throw new UnsolvedSymbolException(this, name);
            }
        } else {
            return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveSymbol(name, typeSolver);
        }
    }
}
