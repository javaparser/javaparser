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
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.none;

/**
 * @author Julio Vilmar Gesser
 */
public final class IfStmt extends Statement {

	private Expression condition;

	private Statement thenStmt;

	private Optional<Statement> elseStmt;

	public IfStmt() {
        this(Range.UNKNOWN,
                new BooleanLiteralExpr(),
                new EmptyStmt(),
                none());
	}

	public IfStmt(final Expression condition, final Statement thenStmt, final Optional<Statement> elseStmt) {
        this(Range.UNKNOWN, condition, thenStmt, elseStmt);
	}

	public IfStmt(Range range,
	              final Expression condition, final Statement thenStmt, final Optional<Statement> elseStmt) {
		super(range);
		setCondition(condition);
		setThenStmt(thenStmt);
		setElseStmt(elseStmt);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Expression getCondition() {
		return condition;
	}

	public Optional<Statement> getElseStmt() {
		return elseStmt;
	}

	public Statement getThenStmt() {
		return thenStmt;
	}

	public IfStmt setCondition(final Expression condition) {
		this.condition = assertNotNull(condition);
		setAsParentNodeOf(this.condition);
		return this;
	}

	public IfStmt setElseStmt(final Optional<Statement> elseStmt) {
		this.elseStmt = assertNotNull(elseStmt);
		setAsParentNodeOf(this.elseStmt);
		return this;
	}

	public IfStmt setThenStmt(final Statement thenStmt) {
		this.thenStmt = assertNotNull(thenStmt);
		setAsParentNodeOf(this.thenStmt);
		return this;
	}
}
