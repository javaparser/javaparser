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
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;
import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserFieldDeclaration implements ResolvedFieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private com.github.javaparser.ast.body.FieldDeclaration wrappedNode;
    private EnumConstantDeclaration enumConstantDeclaration;
    private TypeSolver typeSolver;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        this.variableDeclarator = variableDeclarator;
        this.typeSolver = typeSolver;
        if (!(requireParentNode(variableDeclarator) instanceof com.github.javaparser.ast.body.FieldDeclaration)) {
            throw new IllegalStateException(requireParentNode(variableDeclarator).getClass().getCanonicalName());
        }
        this.wrappedNode = (com.github.javaparser.ast.body.FieldDeclaration) requireParentNode(variableDeclarator);
    }

    public JavaParserFieldDeclaration(EnumConstantDeclaration enumConstantDeclaration, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        this.enumConstantDeclaration = enumConstantDeclaration;
        this.typeSolver = typeSolver;
    }

    @Override
    public ResolvedType getType() {
        if (enumConstantDeclaration != null) {
            com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = (com.github.javaparser.ast.body.EnumDeclaration) requireParentNode(enumConstantDeclaration);
            return new ReferenceTypeImpl(new JavaParserEnumDeclaration(enumDeclaration, typeSolver), typeSolver);
        }
        return JavaParserFacade.get(typeSolver).convert(variableDeclarator.getType(), wrappedNode);
    }

    @Override
    public String getName() {
        if (enumConstantDeclaration != null) {
            return enumConstantDeclaration.getName().getId();
        } else {
            return variableDeclarator.getName().getId();
        }
    }

    @Override
    public boolean isStatic() {
        return wrappedNode.getModifiers().contains(Modifier.STATIC);
    }

    @Override
    public boolean isField() {
        return true;
    }

    /**
     * Returns the JavaParser node associated with this JavaParserFieldDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.FieldDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public String toString() {
        return "JPField{" + getName() + "}";
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return Helper.toAccessLevel(wrappedNode.getModifiers());
    }

    @Override
    public ResolvedTypeDeclaration declaringType() {
        Optional<com.github.javaparser.ast.body.TypeDeclaration> typeDeclaration = wrappedNode.findParent(com.github.javaparser.ast.body.TypeDeclaration.class);
        if (typeDeclaration.isPresent()) {
            return JavaParserFacade.get(typeSolver).getTypeDeclaration(typeDeclaration.get());
        }
        throw new IllegalStateException();
    }
}
