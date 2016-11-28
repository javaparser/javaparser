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
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class UnaryExpr extends Expression implements 
        NodeWithExpression<UnaryExpr> {

	public enum Operator {
		positive, // +
		negative, // -
		preIncrement, // ++
		preDecrement, // --
		not, // !
		inverse, // ~
        postIncrement, // ++
        postDecrement, // --
	}

	private Expression expression;

	private Operator op;

	public UnaryExpr() {
        this(null, new IntegerLiteralExpr(), Operator.postIncrement);
	}

	public UnaryExpr(final Expression expression, final Operator op) {
        this(null, expression, op);
	}

	public UnaryExpr(final Range range, final Expression expression, final Operator op) {
		super(range);
		setExpression(expression);
		setOperator(op);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	@Override
	public Expression getExpression() {
		return expression;
	}

	public Operator getOperator() {
		return op;
	}

    @Override
	public UnaryExpr setExpression(final Expression expr) {
		notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expr);
		this.expression = expr;
		setAsParentNodeOf(this.expression);
		return this;
	}

	public UnaryExpr setOperator(final Operator op) {
		notifyPropertyChange(ObservableProperty.OPERATOR, this.op, op);
		this.op = op;
		return this;
	}
}
