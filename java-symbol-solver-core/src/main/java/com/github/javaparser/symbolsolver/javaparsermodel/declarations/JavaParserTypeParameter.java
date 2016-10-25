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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.FieldDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

public class JavaParserTypeParameter extends AbstractTypeDeclaration implements TypeParameterDeclaration {

    private com.github.javaparser.ast.type.TypeParameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeParameter(com.github.javaparser.ast.type.TypeParameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Collections.emptySet();
    }

    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        return getContext().solveMethod(name, parameterTypes, typeSolver);
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
        return wrappedNode.getName();
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public boolean declaredOnType() {
        return (getParentNode(wrappedNode) instanceof ClassOrInterfaceDeclaration);
    }

    @Override
    public boolean declaredOnMethod() {
        return getParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.MethodDeclaration;
    }

    @Override
    public String getContainerQualifiedName() {
        if (this.declaredOnType()) {
            com.github.javaparser.ast.body.ClassOrInterfaceDeclaration jpTypeDeclaration = (com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) getParentNode(wrappedNode);
            TypeDeclaration typeDeclaration = JavaParserFacade.get(typeSolver).getTypeDeclaration(jpTypeDeclaration);
            return typeDeclaration.getQualifiedName();
        } else {
            com.github.javaparser.ast.body.MethodDeclaration jpMethodDeclaration = (com.github.javaparser.ast.body.MethodDeclaration) getParentNode(wrappedNode);
            MethodDeclaration methodDeclaration = new JavaParserMethodDeclaration(jpMethodDeclaration, typeSolver);
            return methodDeclaration.getQualifiedSignature();
        }
    }

    @Override
    public String getContainerId() {
        if (this.declaredOnType()) {
            com.github.javaparser.ast.body.ClassOrInterfaceDeclaration jpTypeDeclaration = (com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) getParentNode(wrappedNode);
            TypeDeclaration typeDeclaration = JavaParserFacade.get(typeSolver).getTypeDeclaration(jpTypeDeclaration);
            return typeDeclaration.getId();
        } else {
            com.github.javaparser.ast.body.MethodDeclaration jpMethodDeclaration = (com.github.javaparser.ast.body.MethodDeclaration) getParentNode(wrappedNode);
            MethodDeclaration methodDeclaration = new JavaParserMethodDeclaration(jpMethodDeclaration, typeSolver);
            return methodDeclaration.getQualifiedSignature();
        }
    }

    @Override
    public String getQualifiedName() {
        return String.format("%s.%s", getContainerQualifiedName(), getName());
    }

    @Override
    public List<Bound> getBounds(TypeSolver typeSolver) {
        return wrappedNode.getTypeBound().stream().map((astB) -> toBound(astB, typeSolver)).collect(Collectors.toList());
    }

    private Bound toBound(ClassOrInterfaceType classOrInterfaceType, TypeSolver typeSolver) {
        Type type = JavaParserFacade.get(typeSolver).convertToUsage(classOrInterfaceType, classOrInterfaceType);
        Bound bound = Bound.extendsBound(type);
        return bound;
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    public Type getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(Type type) {
        throw new UnsupportedOperationException();
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        return false;
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        return new ArrayList<>();
    }

    @Override
    public List<ReferenceType> getAncestors() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeParameter() {
        return true;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
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
}
