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
import com.github.javaparser.metamodel.IntegerLiteralExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * All ways to specify an int literal.
 * <br/><code>8934</code>
 * <br/><code>0x01</code>
 * <br/><code>022</code>
 * <br/><code>0B10101010</code>
 * <br/><code>99999999L</code>
 * 
 * @author Julio Vilmar Gesser
 */
public class IntegerLiteralExpr extends LiteralStringValueExpr {

    public IntegerLiteralExpr() {
        this(null, "0");
    }

    @AllFieldsConstructor
    public IntegerLiteralExpr(final String value) {
        this(null, value);
    }

    public IntegerLiteralExpr(final Range range, final String value) {
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
    public IntegerLiteralExpr clone() {
        return (IntegerLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public IntegerLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.integerLiteralExprMetaModel;
    }
}
