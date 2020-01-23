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

package org.javaparser.symbolsolver.javassistmodel;

import org.javaparser.ast.expr.Expression;
import org.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.CtMethod;

/**
 * @author Malte Skoruppa
 */
public class JavassistAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private CtMethod annotationMember;
    private TypeSolver typeSolver;

    public JavassistAnnotationMemberDeclaration(CtMethod annotationMember, TypeSolver typeSolver) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        // TODO we should do something like this:
        // AnnotationDefaultAttribute defaultAttribute = (AnnotationDefaultAttribute) annotationMember.getMethodInfo().getAttribute(AnnotationDefaultAttribute.tag);
        // return defaultAttribute != null ? defaultAttribute.getDefaultValue() : null;
        // TODO ...but the interface wants us to return a JavaParser Expression node.
        throw new UnsupportedOperationException("Obtaining the default value of a library annotation member is not supported yet.");
    }

    @Override
    public ResolvedType getType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return annotationMember.getName();
    }
}
