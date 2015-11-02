package me.tomassetti.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;

import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.SymbolReference;

import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.Value;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 31/07/15.
 */
public class FieldAccessContext extends AbstractJavaParserContext<FieldAccessExpr> {

    public FieldAccessContext(FieldAccessExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode(), typeSolver).solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return JavaParserFactory.getContext(wrappedNode.getParentNode(), typeSolver).solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        Expression scope = wrappedNode.getScope();
        if (wrappedNode.getFieldExpr().toString().equals(name)) {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
            if (typeOfScope.isReferenceType()) {
                return typeOfScope.asReferenceTypeUsage().getField(name);
            } else {
                return Optional.empty();
            }
        } else {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
    }
}
