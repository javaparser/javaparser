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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import com.github.javaparser.symbolsolver.declarations.common.MethodDeclarationCommonLogic;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserMethodDeclaration implements ResolvedMethodDeclaration, TypeVariableResolutionCapability {

    private com.github.javaparser.ast.body.MethodDeclaration wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserMethodDeclaration(com.github.javaparser.ast.body.MethodDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public String toString() {
        return "JavaParserMethodDeclaration{" +
                "wrappedNode=" + wrappedNode +
                ", typeSolver=" + typeSolver +
                '}';
    }

    @Override
    public ResolvedReferenceTypeDeclaration declaringType() {
        if (demandParentNode(wrappedNode) instanceof ObjectCreationExpr) {
            ObjectCreationExpr parentNode = (ObjectCreationExpr) demandParentNode(wrappedNode);
            return new JavaParserAnonymousClassDeclaration(parentNode, typeSolver);
        }
        return JavaParserFactory.toTypeDeclaration(demandParentNode(wrappedNode), typeSolver);
    }

    @Override
    public ResolvedType getReturnType() {
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), getContext());
    }

    @Override
    public int getNumberOfParams() {
        return wrappedNode.getParameters().size();
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        if (i < 0 || i >= getNumberOfParams()) {
            throw new IllegalArgumentException(String.format("No param with index %d. Number of params: %d", i, getNumberOfParams()));
        }
        return new JavaParserParameterDeclaration(wrappedNode.getParameters().get(i), typeSolver);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
        return new MethodDeclarationCommonLogic(this, typeSolver).resolveTypeVariables(context, parameterTypes);
    }

    private Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public boolean isAbstract() {
        return !wrappedNode.getBody().isPresent();
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return this.wrappedNode.getTypeParameters().stream().map((astTp) -> new JavaParserTypeParameter(astTp, typeSolver)).collect(Collectors.toList());
    }

    @Override
    public boolean isDefaultMethod() {
        return wrappedNode.isDefault();
    }

    @Override
    public boolean isStatic() {
        return wrappedNode.isStatic();
    }

    /**
     * Returns the JavaParser node associated with this JavaParserMethodDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.MethodDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return wrappedNode.getAccessSpecifier();
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
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getThrownExceptions()
                .get(index), wrappedNode);
    }

    @Override
    public Optional<MethodDeclaration> toAst() {
        return Optional.of(wrappedNode);
    }
}
