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
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

/**
 * @author Julio Vilmar Gesser
 */
public final class ReturnStmt extends Statement {

	private Expression expr;

	public ReturnStmt() {
        this(Range.UNKNOWN, null);
	}

	public ReturnStmt(final Expression expr) {
		this(Range.UNKNOWN, expr);
	}

	public ReturnStmt(Range range, final Expression expr) {
		super(range);
		setExpr(expr);
	}

    /**
     * Will create a NameExpr with the string param
     */
    public ReturnStmt(String expr) {
        this(Range.UNKNOWN, new NameExpr(expr));
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

    public Optional<Expression> getExpr() {
        return Optional.ofNullable(expr);
	}

    /**
     * Sets the expr
     * 
     * @param expr the expr, can be null
     * @return this, the ReturnStmt
     */
	public ReturnStmt setExpr(final Expression expr) {
		notifyPropertyChange(ObservableProperty.EXPR, this.expr, expr);
		this.expr = expr;
		setAsParentNodeOf(this.expr);
		return this;
	}
}
