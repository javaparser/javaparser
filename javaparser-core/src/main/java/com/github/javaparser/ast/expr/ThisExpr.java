/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.expr;

import com.github.javaparser.Position;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class ThisExpr extends Expression {

	private Expression classExpr;

	public ThisExpr() {
	}

	public ThisExpr(final Expression classExpr) {
		setClassExpr(classExpr);
	}

	public ThisExpr(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final Expression classExpr) {
		super(beginLine, beginColumn, endLine, endColumn);
		setClassExpr(classExpr);
	}

	public ThisExpr(Position begin, Position end, Expression classExpr) {
		super(begin, end);
		setClassExpr(classExpr);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Expression getClassExpr() {
		return classExpr;
	}

	public void setClassExpr(final Expression classExpr) {
		this.classExpr = classExpr;
		setAsParentNodeOf(this.classExpr);
	}
}
