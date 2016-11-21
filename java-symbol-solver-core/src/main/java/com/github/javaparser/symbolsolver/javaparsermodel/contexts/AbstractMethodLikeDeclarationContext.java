package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.TypeVariable;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractMethodLikeDeclarationContext
        <T extends Node & NodeWithParameters<T> & NodeWithTypeParameters<T>> extends AbstractJavaParserContext<T> {

    public AbstractMethodLikeDeclarationContext(T wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public final SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference symbolReference = AbstractJavaParserContext.solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public final Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        for (com.github.javaparser.ast.type.TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().getId().equals(name)) {
                return Optional.of(new TypeVariable(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }
        return super.solveGenericType(name, typeSolver);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
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
    public final SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.type.TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(tp, typeSolver));
                }
            }
        }
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public final SymbolReference<MethodDeclaration> solveMethod(
            String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, argumentsTypes, typeSolver);
    }
}
