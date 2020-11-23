/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
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

    @Override
    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference = AbstractJavaParserContext.solveWith(sb, name);
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
    public final SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        // TODO: Is null check required?
        if (wrappedNode.getTypeParameters() != null) {
            for (TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(tp, typeSolver));
                }
            }
        }

        // Local types
        List<TypeDeclaration> localTypes = wrappedNode.findAll(TypeDeclaration.class);
        for (TypeDeclaration<?> localType : localTypes) {
            if (localType.getName().getId().equals(name)) {
                return SymbolReference.solved(JavaParserFacade.get(typeSolver)
                        .getTypeDeclaration(localType));
            } else if (name.startsWith(String.format("%s.", localType.getName()))) {
                return JavaParserFactory.getContext(localType, typeSolver)
                        .solveType(name.substring(localType.getName().getId().length() + 1));
            }
        }

        return solveTypeInParentContext(name);
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }
}
