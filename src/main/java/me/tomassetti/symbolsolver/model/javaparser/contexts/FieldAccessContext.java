package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.SymbolSolver;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.Value;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 31/07/15.
 */
public class FieldAccessContext extends AbstractJavaParserContext<FieldAccessExpr> {

    public FieldAccessContext(FieldAccessExpr wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode()).solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        Expression scope = wrappedNode.getScope();
        TypeUsage typeOfScope = new JavaParserFacade(typeSolver).getType(scope);
        return typeOfScope.getField(name, typeSolver);
    }
}
