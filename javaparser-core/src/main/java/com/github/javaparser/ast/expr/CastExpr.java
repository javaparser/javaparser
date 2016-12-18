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
import com.github.javaparser.ast.nodeTypes.NodeWithExpression;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class CastExpr extends Expression implements
        NodeWithType<CastExpr, Type>,
        NodeWithExpression<CastExpr> {

    private Type type;

    private Expression expression;

    public CastExpr() {
        this(null, new ClassOrInterfaceType(), new NameExpr());
    }

    public CastExpr(Type type, Expression expression) {
        this(null, type, expression);
    }

    public CastExpr(Range range, Type type, Expression expression) {
        super(range);
        setType(type);
        setExpression(expression);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public Expression getExpression() {
        return expression;
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public CastExpr setExpression(Expression expr) {
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expr);
        this.expression = assertNotNull(expr);
        setAsParentNodeOf(this.expression);
        return this;
    }

    @Override
    public CastExpr setType(Type type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = assertNotNull(type);
        setAsParentNodeOf(this.type);
        return this;
    }
}
