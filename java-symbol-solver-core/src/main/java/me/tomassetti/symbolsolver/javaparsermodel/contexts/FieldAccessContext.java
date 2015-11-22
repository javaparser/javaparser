package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;

import java.util.List;
import java.util.Optional;

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
                Optional<TypeUsage> typeUsage = typeOfScope.asReferenceTypeUsage().getFieldType(name);
                if (typeUsage.isPresent()) {
                    return Optional.of(new Value(typeUsage.get(), name, true));
                } else {
                    return Optional.empty();
                }
            } else {
                return Optional.empty();
            }
        } else {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
    }
}
