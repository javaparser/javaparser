/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserConstructorDeclaration<N extends ResolvedReferenceTypeDeclaration> implements ResolvedConstructorDeclaration {

    private N declaringType;
    private com.github.javaparser.ast.body.ConstructorDeclaration wrappedNode;
    private TypeSolver typeSolver;

    JavaParserConstructorDeclaration(N declaringType, com.github.javaparser.ast.body.ConstructorDeclaration wrappedNode,
                                     TypeSolver typeSolver) {
        this.declaringType = declaringType;
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public N declaringType() {
        return declaringType;
    }

    @Override
    public int getNumberOfParams() {
        return this.wrappedNode.getParameters().size();
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        if (i < 0 || i >= getNumberOfParams()) {
            throw new IllegalArgumentException(String.format("No param with index %d. Number of params: %d", i, getNumberOfParams()));
        }
        return new JavaParserParameterDeclaration(wrappedNode.getParameters().get(i), typeSolver);
    }

    @Override
    public String getName() {
        return this.declaringType.getName();
    }

    /**
     * Returns the JavaParser node associated with this JavaParserConstructorDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.ConstructorDeclaration getWrappedNode() {
        return wrappedNode;
    }
    
    @Override
    public AccessSpecifier accessSpecifier() {
        return wrappedNode.getAccessSpecifier();
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return this.wrappedNode.getTypeParameters().stream().map((astTp) -> new JavaParserTypeParameter(astTp, typeSolver)).collect(Collectors.toList());
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        return wrappedNode.getThrownExceptions().size();
    }

    @Override
    public ResolvedType getSpecifiedException(int index) {
        if (index < 0 || index >= getNumberOfSpecifiedExceptions()) {
            throw new IllegalArgumentException(String.format("No exception with index %d. Number of exceptions: %d",
                    index, getNumberOfSpecifiedExceptions()));
        }
        return JavaParserFacade.get(typeSolver)
                .convert(wrappedNode.getThrownExceptions().get(index), wrappedNode);
    }

    @Override
    public Optional<ConstructorDeclaration> toAst() {
        return Optional.of(wrappedNode);
    }
}
