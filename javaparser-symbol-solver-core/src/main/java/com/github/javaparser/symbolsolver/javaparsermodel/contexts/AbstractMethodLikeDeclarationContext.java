/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.SymbolDeclarator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractMethodLikeDeclarationContext<
                T extends Node & NodeWithParameters<T> & NodeWithTypeParameters<T>>
        extends AbstractJavaParserContext<T> {

    /**
     * The types declared inside a method or constructor, kept on its node: every type name looked up inside it is
     * checked against them, and finding them means walking the whole declaration.
     */
    private static final DataKey<LocalTypes> LOCAL_TYPES = new DataKey<LocalTypes>() {};

    public AbstractMethodLikeDeclarationContext(T wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference =
                    AbstractJavaParserContext.solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolInParentContext(name);
    }

    @Override
    public final Optional<ResolvedType> solveGenericType(String name) {
        // First check if the method-like declaration has type parameters defined.
        // For example: {@code public <T> boolean containsAll(Collection<T> c);}
        for (TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().getId().equals(name)) {
                return Optional.of(new ResolvedTypeVariable(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }

        // If no generic types on the method declaration, continue to solve elsewhere as usual.
        return solveGenericTypeInParentContext(name);
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
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public final SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        // TODO: Is null check required?
        if (wrappedNode.getTypeParameters() != null) {
            for (TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(tp, typeSolver));
                }
            }
        }

        // Local types
        for (TypeDeclaration<?> localType : localTypes()) {
            if (localType.getName().getId().equals(name)) {
                return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(localType));
            }
            if (name.startsWith(String.format("%s.", localType.getName()))) {
                return JavaParserFactory.getContext(localType, typeSolver)
                        .solveType(name.substring(localType.getName().getId().length() + 1));
            }
        }

        return solveTypeInParentContext(name, typeArguments);
    }

    /**
     * The types declared inside the wrapped node, in pre-order. They are found once and then kept on the node, so,
     * like the types the facade keeps on nodes, they reflect the node as it was when first needed.
     */
    private List<TypeDeclaration> localTypes() {
        Optional<LocalTypes> kept = wrappedNode.findData(LOCAL_TYPES);
        // A clone carries the data of the node it was cloned from, but its local types are its own nodes.
        if (kept.isPresent() && kept.get().declaration == wrappedNode) {
            return kept.get().types;
        }
        List<TypeDeclaration> types = wrappedNode.findAll(TypeDeclaration.class);
        wrappedNode.setData(LOCAL_TYPES, new LocalTypes(wrappedNode, types));
        return types;
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }

    /**
     * The types declared inside a method or constructor, with the declaration they were found in.
     */
    private static final class LocalTypes {

        private final Node declaration;

        private final List<TypeDeclaration> types;

        private LocalTypes(Node declaration, List<TypeDeclaration> types) {
            this.declaration = declaration;
            this.types = types;
        }
    }
}
