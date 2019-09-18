/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
