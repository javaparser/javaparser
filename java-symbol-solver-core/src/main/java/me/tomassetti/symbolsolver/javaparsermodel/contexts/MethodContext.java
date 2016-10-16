package me.tomassetti.symbolsolver.javaparsermodel.contexts;


import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.TypeParameter;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;

import java.util.List;
import java.util.Optional;

public class MethodContext extends AbstractJavaParserContext<MethodDeclaration> {

    public MethodContext(MethodDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference symbolReference = solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(new TypeParameter(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }
        return super.solveGenericType(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            Optional<Value> symbolReference = solveWithAsValue(sb, name, typeSolver);
            if (symbolReference.isPresent()) {
                // Perform parameter type substitution as needed
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(tp, typeSolver));
                }
            }
        }
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

}
