/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import static com.github.javaparser.Position.pos;

import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.TypedNode;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class InstanceOfExpr extends Expression implements TypedNode<InstanceOfExpr> {

	private Expression expr;

	private Type type;

	public InstanceOfExpr() {
	}

	public InstanceOfExpr(final Expression expr, final Type type) {
		setExpr(expr);
		setType(type);
	}

	/**
	 * @deprecated prefer using Range objects.
	 */
	@Deprecated
	public InstanceOfExpr(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
	                      final Expression expr, final Type type) {
		this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), expr, type);
	}
	
	public InstanceOfExpr(final Range range, final Expression expr, final Type type) {
		super(range);
		setExpr(expr);
		setType(type);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Expression getExpr() {
		return expr;
	}

	@Override
	public Type getType() {
		return type;
	}

	public void setExpr(final Expression expr) {
		this.expr = expr;
		setAsParentNodeOf(this.expr);
	}

	@Override
    public InstanceOfExpr setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
        return this;
	}
}
