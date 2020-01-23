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

import org.javaparser.ast.body.EnumDeclaration;
import org.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

import static org.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserEnumConstantDeclaration implements ResolvedEnumConstantDeclaration {

    private TypeSolver typeSolver;
    private org.javaparser.ast.body.EnumConstantDeclaration wrappedNode;

    public JavaParserEnumConstantDeclaration(org.javaparser.ast.body.EnumConstantDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public ResolvedType getType() {
        return new ReferenceTypeImpl(new JavaParserEnumDeclaration((EnumDeclaration) demandParentNode(wrappedNode), typeSolver), typeSolver);
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    /**
     * Returns the JavaParser node associated with this JavaParserEnumConstantDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public org.javaparser.ast.body.EnumConstantDeclaration getWrappedNode() {
        return wrappedNode;
    }

}
