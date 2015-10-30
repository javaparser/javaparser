package me.tomassetti.symbolsolver.resolution.javaparser.contexts;


import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.MethodDeclaration;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.resolution.javaparser.declarations.JavaParserTypeParameter;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsageOfTypeParameter;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public class MethodContext extends AbstractJavaParserContext<MethodDeclaration> {


    public MethodContext(MethodDeclaration wrappedNode) {
        super(wrappedNode);
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
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().equals(name)){
                return Optional.of(new TypeUsageOfTypeParameter(new JavaParserTypeParameter(tp)));
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
                    return SymbolReference.solved(new JavaParserTypeParameter(tp));
                }
            }
        }
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        /*if (wrappedNode.getName().equals(name)) {
            // TODO understand if signature is compatible
            throw new UnsupportedOperationException();
        }*/

        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

}
