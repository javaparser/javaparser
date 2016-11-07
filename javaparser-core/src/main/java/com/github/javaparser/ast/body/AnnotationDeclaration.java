/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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
 
package com.github.javaparser.ast.body;

import java.util.List;

import java.util.EnumSet;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.ast.NodeList.*;
import static com.github.javaparser.ast.expr.NameExpr.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class AnnotationDeclaration extends TypeDeclaration<AnnotationDeclaration> {

    public AnnotationDeclaration() {
        this(Range.UNKNOWN,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new SimpleName(),
                new NodeList<>());
    }

    public AnnotationDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(Range.UNKNOWN,
                modifiers,
                new NodeList<>(),
                new SimpleName(name),
                new NodeList<>());
    }

    public AnnotationDeclaration(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name,
                                 NodeList<BodyDeclaration<?>> members) {
        this(Range.UNKNOWN,
                modifiers,
                annotations,
                name,
                members);
    }

    public AnnotationDeclaration(Range range, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name,
                                 NodeList<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }
}
