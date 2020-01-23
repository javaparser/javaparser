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

package org.javaparser.symbolsolver.javaparsermodel.declarations;

import org.javaparser.ast.AccessSpecifier;
import org.javaparser.ast.Modifier;
import org.javaparser.ast.body.TypeDeclaration;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import org.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Optional;

import static org.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserFieldDeclaration implements ResolvedFieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private org.javaparser.ast.body.FieldDeclaration wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        this.variableDeclarator = variableDeclarator;
        this.typeSolver = typeSolver;
        if (!(demandParentNode(variableDeclarator) instanceof org.javaparser.ast.body.FieldDeclaration)) {
            throw new IllegalStateException(demandParentNode(variableDeclarator).getClass().getCanonicalName());
        }
        this.wrappedNode = (org.javaparser.ast.body.FieldDeclaration) demandParentNode(variableDeclarator);
    }

    @Override
    public ResolvedType getType() {
        return JavaParserFacade.get(typeSolver).convert(variableDeclarator.getType(), wrappedNode);
    }

    @Override
    public String getName() {
        return variableDeclarator.getName().getId();
    }

    @Override
    public boolean isStatic() {
        return wrappedNode.hasModifier(Modifier.Keyword.STATIC);
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
    public org.javaparser.ast.body.FieldDeclaration getWrappedNode() {
        return wrappedNode;
    }

    public VariableDeclarator getVariableDeclarator() {
        return variableDeclarator;
    }

    @Override
    public String toString() {
        return "JavaParserFieldDeclaration{" + getName() + "}";
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return wrappedNode.getAccessSpecifier();
    }

    @Override
    public ResolvedTypeDeclaration declaringType() {
        Optional<TypeDeclaration> typeDeclaration = wrappedNode.findAncestor(TypeDeclaration.class);
        if (typeDeclaration.isPresent()) {
            return JavaParserFacade.get(typeSolver).getTypeDeclaration(typeDeclaration.get());
        }
        throw new IllegalStateException();
    }
}
