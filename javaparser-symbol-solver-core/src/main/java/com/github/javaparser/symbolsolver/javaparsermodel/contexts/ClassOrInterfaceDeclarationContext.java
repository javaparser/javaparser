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

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;

/**
 * @author Federico Tomassetti
 */
public class ClassOrInterfaceDeclarationContext extends AbstractJavaParserContext<ClassOrInterfaceDeclaration> {

    private JavaParserTypeDeclarationAdapter javaParserTypeDeclarationAdapter;

    ///
    /// Constructors
    ///

    public ClassOrInterfaceDeclarationContext(ClassOrInterfaceDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
        this.javaParserTypeDeclarationAdapter = new JavaParserTypeDeclarationAdapter(wrappedNode, typeSolver,
                getDeclaration(), this);
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
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return javaParserTypeDeclarationAdapter.solveType(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return javaParserTypeDeclarationAdapter.solveMethod(name, argumentsTypes, staticOnly);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        return javaParserTypeDeclarationAdapter.solveConstructor(argumentsTypes);
    }

    @Override
    public List<ResolvedFieldDeclaration> fieldsExposedToChild(Node child) {
        List<ResolvedFieldDeclaration> fields = new LinkedList<>();
        fields.addAll(this.wrappedNode.resolve().getDeclaredFields());
        this.wrappedNode.getExtendedTypes().forEach(i -> fields.addAll(i.resolve().getAllFieldsVisibleToInheritors()));
        this.wrappedNode.getImplementedTypes().forEach(i -> fields.addAll(i.resolve().getAllFieldsVisibleToInheritors()));
        return fields;
    }

    ///
    /// Private methods
    ///

    private ResolvedReferenceTypeDeclaration getDeclaration() {
        return JavaParserFacade.get(typeSolver).getTypeDeclaration(this.wrappedNode);
    }
}
