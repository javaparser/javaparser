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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.utils.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class ExplicitConstructorInvocationStmt extends Statement {

	private List<Type> typeArgsList;

	private boolean isThis;

	private Expression expr;

	private List<Expression> argsList;

	public ExplicitConstructorInvocationStmt() {
	}

	public ExplicitConstructorInvocationStmt(final boolean isThis,
			final Expression expr, final List<Expression> argsList) {
		setThis(isThis);
		setExpr(expr);
		setArgsList(argsList);
	}

	public ExplicitConstructorInvocationStmt(Range range,
	                                         final List<Type> typeArgsList, final boolean isThis,
	                                         final Expression expr, final List<Expression> argsList) {
		super(range);
		setTypeArgsList(typeArgsList);
		setThis(isThis);
		setExpr(expr);
		setArgsList(argsList);
	}

	@Override
	public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<Expression> getArgsList() {
        argsList = ensureNotNull(argsList);
        return argsList;
	}

	public Expression getExpr() {
		return expr;
	}

	public List<Type> getTypeArgsList() {
        typeArgsList = ensureNotNull(typeArgsList);
        return typeArgsList;
	}

	public boolean isThis() {
		return isThis;
	}

	public void setArgsList(final List<Expression> argsList) {
		this.argsList = argsList;
		setAsParentNodeOf(this.argsList);
	}

	public void setExpr(final Expression expr) {
		this.expr = expr;
		setAsParentNodeOf(this.expr);
	}

	public void setThis(final boolean isThis) {
		this.isThis = isThis;
	}

	public void setTypeArgsList(final List<Type> typeArgsList) {
		this.typeArgsList = typeArgsList;
		setAsParentNodeOf(this.typeArgsList);
	}
}
