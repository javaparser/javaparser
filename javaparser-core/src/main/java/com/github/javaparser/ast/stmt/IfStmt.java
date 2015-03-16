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

package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class IfStmt extends Statement {

	private Expression condition;

	private Statement thenStmt;

	private Statement elseStmt;

	public IfStmt() {
	}

	public IfStmt(final Expression condition, final Statement thenStmt, final Statement elseStmt) {
		setCondition(condition);
		setThenStmt(thenStmt);
		setElseStmt(elseStmt);
	}

	public IfStmt(Lexeme first, Lexeme last,
			final Expression condition, final Statement thenStmt, final Statement elseStmt) {
		super(first, last);
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

	public Statement getElseStmt() {
		return elseStmt;
	}

	public Statement getThenStmt() {
		return thenStmt;
	}

	public void setCondition(final Expression condition) {
		this.condition = condition;
		setAsParentNodeOf(this.condition);
	}

	public void setElseStmt(final Statement elseStmt) {
		this.elseStmt = elseStmt;
		setAsParentNodeOf(this.elseStmt);
	}

	public void setThenStmt(final Statement thenStmt) {
		this.thenStmt = thenStmt;
		setAsParentNodeOf(this.thenStmt);
	}
}
