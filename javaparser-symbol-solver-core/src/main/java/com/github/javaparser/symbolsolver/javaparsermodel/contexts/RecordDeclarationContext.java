/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserRecordDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class RecordDeclarationContext extends AbstractJavaParserContext<RecordDeclaration> {

    private JavaParserTypeDeclarationAdapter javaParserTypeDeclarationAdapter;

    ///
    /// Constructors
    ///

    public RecordDeclarationContext(RecordDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
        this.javaParserTypeDeclarationAdapter =
                new JavaParserTypeDeclarationAdapter(wrappedNode, typeSolver, getDeclaration(), this);
    }

    ///
    /// Public methods
    ///

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        if (typeSolver == null) throw new IllegalArgumentException();

        if (this.getDeclaration().hasVisibleField(name)) {
            return SymbolReference.solved(this.getDeclaration().getVisibleField(name));
        }

        // then to parent
        return solveSymbolInParentContext(name);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        if (typeSolver == null) throw new IllegalArgumentException();

        if (this.getDeclaration().hasField(name)) {
            return Optional.of(Value.from(this.getDeclaration().getField(name)));
        }

        // then to parent
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public Optional<ResolvedType> solveGenericType(String name) {
        // First check if the method-like declaration has type parameters defined.
        // For example: {@code public <T> boolean containsAll(Collection<T> c);}
        for (TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().getId().equals(name)) {
                return Optional.of(new ResolvedTypeVariable(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }

        // If no generic types on the method declaration, continue to solve as usual.
        return solveGenericTypeInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        return javaParserTypeDeclarationAdapter.solveType(name, typeArguments);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        SymbolReference<ResolvedMethodDeclaration> resolvedExplicitMethod =
                javaParserTypeDeclarationAdapter.solveMethod(name, argumentsTypes, staticOnly);

        if (!resolvedExplicitMethod.isSolved() && argumentsTypes.isEmpty()) {
            // If the method could not be resolved and has no arguments, then it could be an implicit getter for
            // a record parameter.
            Optional<Parameter> matchingParameter = wrappedNode.getParameters().stream()
                    .filter(parameter -> parameter.getNameAsString().equals(name))
                    .findFirst();

            if (matchingParameter.isPresent()) {
                ResolvedMethodDeclaration resolvedMethod = new JavaParserRecordDeclaration.ImplicitGetterMethod(
                        matchingParameter.get(), wrappedNode, typeSolver);
                return SymbolReference.solved(resolvedMethod);
            }
        }

        return resolvedExplicitMethod;
    }

    public SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        return javaParserTypeDeclarationAdapter.solveConstructor(argumentsTypes);
    }

    @Override
    public List<ResolvedFieldDeclaration> fieldsExposedToChild(Node child) {
        List<ResolvedFieldDeclaration> fields = new LinkedList<>();
        fields.addAll(this.wrappedNode.resolve().getDeclaredFields());
        this.wrappedNode
                .getImplementedTypes()
                .forEach(i -> fields.addAll(i.resolve().asReferenceType().getAllFieldsVisibleToInheritors()));
        return fields;
    }

    ///
    /// Private methods
    ///

    private ResolvedReferenceTypeDeclaration getDeclaration() {
        return JavaParserFacade.get(typeSolver).getTypeDeclaration(this.wrappedNode);
    }
}
