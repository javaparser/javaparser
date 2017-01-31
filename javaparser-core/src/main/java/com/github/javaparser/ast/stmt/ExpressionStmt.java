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
package com.github.javaparser.ast.stmt;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithExpression;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Used to wrap an expression so that it can take the place of a statement.
 *
 * @author Julio Vilmar Gesser
 */
public final class ExpressionStmt extends Statement implements NodeWithExpression<ExpressionStmt> {

    private Expression expression;

    public ExpressionStmt() {
        this(null, new BooleanLiteralExpr());
    }

    @AllFieldsConstructor
    public ExpressionStmt(final Expression expression) {
        this(null, expression);
    }

    public ExpressionStmt(Range range, final Expression expression) {
        super(range);
        setExpression(expression);
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
    public Expression getExpression() {
        return expression;
    }

    @Override
    public ExpressionStmt setExpression(final Expression expression) {
        assertNotNull(expression);
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }
}

