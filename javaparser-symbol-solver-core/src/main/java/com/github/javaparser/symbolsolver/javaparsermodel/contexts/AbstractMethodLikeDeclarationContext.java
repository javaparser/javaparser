package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
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

    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference = AbstractJavaParserContext.solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name);
    }

    @Override
    public final Optional<ResolvedType> solveGenericType(String name) {
        for (com.github.javaparser.ast.type.TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().getId().equals(name)) {
                return Optional.of(new ResolvedTypeVariable(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }
        return super.solveGenericType(name);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            Optional<Value> symbolReference = solveWithAsValue(sb, name);
            if (symbolReference.isPresent()) {
                // Perform parameter type substitution as needed
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name);
    }

    @Override
    public final SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.type.TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(tp, typeSolver));
                }
            }
        }
        
        // Local types
        List<com.github.javaparser.ast.body.TypeDeclaration> localTypes = wrappedNode.findAll(
                com.github.javaparser.ast.body.TypeDeclaration.class);
        for (com.github.javaparser.ast.body.TypeDeclaration<?> localType : localTypes) {
            if (localType.getName().getId().equals(name)) {
                return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(localType));
            } else if (name.startsWith(String.format("%s.", localType.getName()))) {
                return JavaParserFactory.getContext(localType, typeSolver).solveType(
                        name.substring(localType.getName().getId().length() + 1));
            }
        }
        
        return getParent().solveType(name);
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }
}
