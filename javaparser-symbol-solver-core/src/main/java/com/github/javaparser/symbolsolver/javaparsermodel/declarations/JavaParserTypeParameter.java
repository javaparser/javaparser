/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;

import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.resolution.Navigator.demandParentNode;


/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeParameter extends AbstractTypeDeclaration implements ResolvedTypeParameterDeclaration {

    private com.github.javaparser.ast.type.TypeParameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeParameter(com.github.javaparser.ast.type.TypeParameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return Collections.emptySet();
    }

    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes) {
        return getContext().solveMethod(name, parameterTypes, false);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof JavaParserTypeParameter)) return false;

        JavaParserTypeParameter that = (JavaParserTypeParameter) o;

        if (wrappedNode != null ? !wrappedNode.equals(that.wrappedNode) : that.wrappedNode != null) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = wrappedNode != null ? wrappedNode.hashCode() : 0;
        result = 31 * result + (typeSolver != null ? typeSolver.hashCode() : 0);
        return result;
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other));
    }

    @Override
    public String getContainerQualifiedName() {
        ResolvedTypeParametrizable container = getContainer();
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return ((ResolvedReferenceTypeDeclaration) container).getQualifiedName();
        }
            if (container instanceof JavaParserConstructorDeclaration) {
            return ((JavaParserConstructorDeclaration) container).getQualifiedSignature();
        }
        return ((JavaParserMethodDeclaration) container).getQualifiedSignature();
    }

    @Override
    public String getContainerId() {
        ResolvedTypeParametrizable container = getContainer();
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return ((ResolvedReferenceTypeDeclaration) container).getId();
        }
            if (container instanceof JavaParserConstructorDeclaration) {
            return ((JavaParserConstructorDeclaration) container).getQualifiedSignature();
        }
        return ((JavaParserMethodDeclaration) container).getQualifiedSignature();
    }

    @Override
    public ResolvedTypeParametrizable getContainer() {
        Node parentNode = demandParentNode(wrappedNode);
        if (parentNode instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            com.github.javaparser.ast.body.ClassOrInterfaceDeclaration jpTypeDeclaration = (com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) parentNode;
            return JavaParserFacade.get(typeSolver).getTypeDeclaration(jpTypeDeclaration);
        }
        if (parentNode instanceof com.github.javaparser.ast.body.ConstructorDeclaration){
            com.github.javaparser.ast.body.ConstructorDeclaration jpConstructorDeclaration = (com.github.javaparser.ast.body.ConstructorDeclaration) parentNode;
            Optional<ClassOrInterfaceDeclaration> jpTypeDeclaration = jpConstructorDeclaration.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class);
            if (jpTypeDeclaration.isPresent()) {
                ResolvedReferenceTypeDeclaration typeDeclaration = JavaParserFacade.get(typeSolver).getTypeDeclaration(jpTypeDeclaration.get());
                if (typeDeclaration.isClass()) {
                    return new JavaParserConstructorDeclaration(typeDeclaration.asClass(), jpConstructorDeclaration, typeSolver);
                }
            }
        } else {
            com.github.javaparser.ast.body.MethodDeclaration jpMethodDeclaration = (com.github.javaparser.ast.body.MethodDeclaration) parentNode;
            return new JavaParserMethodDeclaration(jpMethodDeclaration, typeSolver);
        }
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQualifiedName() {
        return String.format("%s.%s", getContainerQualifiedName(), getName());
    }

    @Override
    public List<Bound> getBounds() {
        return wrappedNode.getTypeBound().stream().map((astB) -> toBound(astB, typeSolver)).collect(Collectors.toList());
    }

    private Bound toBound(ClassOrInterfaceType classOrInterfaceType, TypeSolver typeSolver) {
        ResolvedType type = JavaParserFacade.get(typeSolver).convertToUsage(classOrInterfaceType);
        return Bound.extendsBound(type);
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    public ResolvedType getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ResolvedFieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        return false;
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        return new ArrayList<>();
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeParameter() {
        return true;
    }

    @Override
    public ResolvedTypeParameterDeclaration asTypeParameter() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    /**
     * Returns the JavaParser node associated with this JavaParserTypeParameter.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.type.TypeParameter getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public String toString() {
        return "JPTypeParameter(" + wrappedNode.getName() + ", bounds=" + wrappedNode.getTypeBound() + ")";
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        ResolvedTypeParametrizable container = getContainer();
        if (container instanceof ResolvedReferenceTypeDeclaration) {
            return Optional.of((ResolvedReferenceTypeDeclaration) container);
        }
        return Optional.empty();
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Collections.emptyList();
    }

    @Override
    public ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

}
