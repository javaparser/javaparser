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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.ast.expr.NameExpr.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class NormalAnnotationExpr extends AnnotationExpr {

    private NodeList<MemberValuePair> pairs;

    public NormalAnnotationExpr() {
        this(Range.UNKNOWN, new NameExpr(), new NodeList<>());
    }

    public NormalAnnotationExpr(final NameExpr name, final NodeList<MemberValuePair> pairs) {
        this(Range.UNKNOWN, name, pairs);
    }

    public NormalAnnotationExpr(final Range range, final NameExpr name, final NodeList<MemberValuePair> pairs) {
        super(range, name);
        setPairs(pairs);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public NodeList<MemberValuePair> getPairs() {
        return pairs;
    }

    public NormalAnnotationExpr setPairs(final NodeList<MemberValuePair> pairs) {
        this.pairs = assertNotNull(pairs);
        setAsParentNodeOf(this.pairs);
        return this;
    }

    /**
     * adds a pair to this annotation
     * 
     * @return this, the {@link NormalAnnotationExpr}
     */
    public NormalAnnotationExpr addPair(String key, String value) {
        return addPair(key, name(value));
    }

    /**
     * adds a pair to this annotation
     * 
     * @return this, the {@link NormalAnnotationExpr}
     */
    public NormalAnnotationExpr addPair(String key, NameExpr value) {
        MemberValuePair memberValuePair = new MemberValuePair(key, value);
        getPairs().add(memberValuePair);
        memberValuePair.setParentNode(this);
        return this;
    }
}
