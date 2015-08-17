package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.expr.MethodCallExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 31/07/15.
 */
public class MethodCallExprContext extends AbstractJavaParserContext<MethodCallExpr> {

    public MethodCallExprContext(MethodCallExpr wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        if (wrappedNode.getTypeArgs() != null) {
            throw new UnsupportedOperationException(name);
        }
        TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
        return typeOfScope.solveGenericType(name);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope() != null) {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
            return typeOfScope.solveMethodAsUsage(name, parameterTypes, typeSolver, this);
        } else {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
            return typeOfScope.solveMethodAsUsage(name, parameterTypes, typeSolver, this);
        }
    }

    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope() != null) {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
            return typeOfScope.solveMethod(name, parameterTypes, typeSolver);
        } else {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
            return typeOfScope.solveMethod(name, parameterTypes, typeSolver);
        }
    }
}
