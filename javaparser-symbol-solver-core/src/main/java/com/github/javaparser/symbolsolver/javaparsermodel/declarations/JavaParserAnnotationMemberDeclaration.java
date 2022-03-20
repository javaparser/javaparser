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

import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * @author Federico Tomassetti
 */
public class JavaParserAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private com.github.javaparser.ast.body.AnnotationMemberDeclaration wrappedNode;
    private TypeSolver typeSolver;

    public AnnotationMemberDeclaration getWrappedNode() {
        return wrappedNode;
    }

    public JavaParserAnnotationMemberDeclaration(AnnotationMemberDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        return wrappedNode.getDefaultValue().orElse(null);
    }

    @Override
    public ResolvedType getType() {
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), getContext());
    }

    @Override
    public String getName() {
        return wrappedNode.getNameAsString();
    }

    private Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }
}
