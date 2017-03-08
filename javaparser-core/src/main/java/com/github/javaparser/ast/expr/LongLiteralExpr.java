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

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LongLiteralExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * All ways to specify a long literal.
 * <br/><code>8934l</code>
 * <br/><code>0x01L</code>
 * <br/><code>022l</code>
 * <br/><code>0B10101010L</code>
 * <br/><code>99999999L</code>
 *
 * @author Julio Vilmar Gesser
 */
public class LongLiteralExpr extends LiteralStringValueExpr {

    public LongLiteralExpr() {
        this(null, "0");
    }

    @AllFieldsConstructor
    public LongLiteralExpr(final String value) {
        this(null, value);
    }

    public LongLiteralExpr(final Range range, final String value) {
        super(range, value);
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
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public LongLiteralExpr clone() {
        return (LongLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public LongLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.longLiteralExprMetaModel;
    }
}
