package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.expr.MethodCallExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope() != null) {
            TypeUsage typeOfScope = new JavaParserFacade(typeSolver).getType(wrappedNode.getScope());
            return typeOfScope.solveMethod(name, parameterTypes);
        } else {
            return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveSymbol(name, typeSolver);
        }
    }
}
