/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.core.resolution;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AbstractJavaParserContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.Value;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Context is very similar to scope.
 * In the context we look for solving symbols.
 *
 * @author Federico Tomassetti
 */
public interface Context {

    Context getParent();

    /* Type resolution */

    default Optional<ResolvedType> solveGenericType(String name) {
        return Optional.empty();
    }

    default SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        Context parent = getParent();
        if (parent == null) {
            return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
        } else {
            return parent.solveType(name);
        }
    }

    /* Symbol resolution */

    default SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        return getParent().solveSymbol(name);
    }

    default Optional<Value> solveSymbolAsValue(String name) {
        SymbolReference<? extends ResolvedValueDeclaration> ref = solveSymbol(name);
        if (ref.isSolved()) {
            Value value = Value.from(ref.getCorrespondingDeclaration());
            return Optional.of(value);
        } else {
            return Optional.empty();
        }
    }

    /**
     * The local variables that are declared in this immediate context and made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     * The parameters that are declared in this immediate context and made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<Parameter> parametersExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     * The fields that are declared and in this immediate context made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<ResolvedFieldDeclaration> fieldsExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     * Aim to resolve the given name by looking for a variable matching it.
     *
     * To do it consider local variables that are visible in a certain scope as defined in JLS 6.3. Scope of a Declaration.
     *
     * 1. The scope of a local variable declaration in a block (§14.4) is the rest of the block in which the declaration
     * appears, starting with its own initializer and including any further declarators to the right in the local
     * variable declaration statement.
     *
     * 2. The scope of a local variable declared in the ForInit part of a basic for statement (§14.14.1) includes all
     * of the following:
     * 2.1 Its own initializer
     * 2.2 Any further declarators to the right in the ForInit part of the for statement
     * 2.3 The Expression and ForUpdate parts of the for statement
     * 2.4 The contained Statement
     *
     * 3. The scope of a local variable declared in the FormalParameter part of an enhanced for statement (§14.14.2) is
     * the contained Statement.
     * 4. The scope of a parameter of an exception handler that is declared in a catch clause of a try statement
     * (§14.20) is the entire block associated with the catch.
     *
     * 5. The scope of a variable declared in the ResourceSpecification of a try-with-resources statement (§14.20.3) is
     * from the declaration rightward over the remainder of the ResourceSpecification and the entire try block
     * associated with the try-with-resources statement.
     */
    default Optional<VariableDeclarator> localVariableDeclarationInScope(String name) {
        if (getParent() == null) {
            return Optional.empty();
        }
        Optional<VariableDeclarator> localRes = getParent().localVariablesExposedToChild(((AbstractJavaParserContext)this)
                .getWrappedNode()).stream().filter(vd -> vd.getNameAsString().equals(name)).findFirst();
        if (localRes.isPresent()) {
            return localRes;
        }

        return getParent().localVariableDeclarationInScope(name);
    }

    default Optional<Parameter> parameterDeclarationInScope(String name) {
        if (getParent() == null) {
            return Optional.empty();
        }
        Optional<Parameter> localRes = getParent().parametersExposedToChild(((AbstractJavaParserContext)this)
                .getWrappedNode()).stream().filter(vd -> vd.getNameAsString().equals(name)).findFirst();
        if (localRes.isPresent()) {
            return localRes;
        }

        return getParent().parameterDeclarationInScope(name);
    }

    default Optional<ResolvedFieldDeclaration> fieldDeclarationInScope(String name) {
        if (getParent() == null) {
            return Optional.empty();
        }
        Optional<ResolvedFieldDeclaration> localRes = getParent().fieldsExposedToChild(((AbstractJavaParserContext)this)
                .getWrappedNode()).stream().filter(vd -> vd.getName().equals(name)).findFirst();
        if (localRes.isPresent()) {
            return localRes;
        }

        return getParent().fieldDeclarationInScope(name);
    }

    /* Constructor resolution */

    /**
     * We find the method declaration which is the best match for the given name and list of typeParametersValues.
     */
    default SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        throw new IllegalArgumentException("Constructor resolution is available only on Class Context");
    }

    /* Methods resolution */

    /**
     * We find the method declaration which is the best match for the given name and list of typeParametersValues.
     */
    default SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                   boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, staticOnly);
    }

    /**
     * Similar to solveMethod but we return a MethodUsage. A MethodUsage corresponds to a MethodDeclaration plus the
     * resolved type variables.
     */
    default Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes) {
        SymbolReference<ResolvedMethodDeclaration> methodSolved = solveMethod(name, argumentsTypes, false);
        if (methodSolved.isSolved()) {
            ResolvedMethodDeclaration methodDeclaration = methodSolved.getCorrespondingDeclaration();

            MethodUsage methodUsage;
            if (methodDeclaration instanceof TypeVariableResolutionCapability) {
                methodUsage = ((TypeVariableResolutionCapability) methodDeclaration)
                                      .resolveTypeVariables(this, argumentsTypes);
            } else {
                throw new UnsupportedOperationException("Resolved method declarations should have the " +
                                                        TypeVariableResolutionCapability.class.getName() + ".");
            }

            return Optional.of(methodUsage);
        } else {
            return Optional.empty();
        }
    }

}
