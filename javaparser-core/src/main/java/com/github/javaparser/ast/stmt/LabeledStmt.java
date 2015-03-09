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

import com.github.javaparser.Position;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class LabeledStmt extends Statement {

	private String label;

	private Statement stmt;

	public LabeledStmt() {
	}

	public LabeledStmt(final String label, final Statement stmt) {
		setLabel(label);
		setStmt(stmt);
	}

	public LabeledStmt(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final String label, final Statement stmt) {
		super(beginLine, beginColumn, endLine, endColumn);
		setLabel(label);
		setStmt(stmt);
	}

	public LabeledStmt(Position begin, Position end, final String label, final Statement stmt) {
		super(begin, end);
		setLabel(label);
		setStmt(stmt);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public String getLabel() {
		return label;
	}

	public Statement getStmt() {
		return stmt;
	}

	public void setLabel(final String label) {
		this.label = label;
	}

	public void setStmt(final Statement stmt) {
		this.stmt = stmt;
		setAsParentNodeOf(this.stmt);
	}
}
