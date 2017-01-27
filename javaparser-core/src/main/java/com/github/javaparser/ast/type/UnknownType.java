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

package com.github.javaparser.ast.type;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * An unknown parameter type object. It plays the role of a null object for
 * lambda parameters that have no explicit type declared. As such, it has no
 * lexical representation and hence gets no comment attributed.
 *
 * <br/>In <code>DoubleToIntFunction d = <b>x</b> -> (int)x + 1;</code> the x parameter in bold has type UnknownType.
 * 
 * @author Didier Villevalois
 */
public final class UnknownType extends Type {

    public UnknownType() {
        super(null, new NodeList<>());
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public UnknownType setAnnotations(NodeList<AnnotationExpr> annotations) {
        if (annotations.size() > 0) {
            throw new IllegalStateException("Inferred lambda types cannot be annotated.");
        }

        return (UnknownType) super.setAnnotations(annotations);
    }
}
