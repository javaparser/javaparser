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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.none;

/**
 * @author Julio Vilmar Gesser
 */
public final class SwitchEntryStmt extends Statement implements NodeWithStatements<SwitchEntryStmt> {

	private Optional<Expression> label;

	private NodeList<Statement> stmts;

	public SwitchEntryStmt() {
		this(Range.UNKNOWN, none(), new NodeList<>());
	}

	public SwitchEntryStmt(final Optional<Expression> label, final NodeList<Statement> stmts) {
		this(Range.UNKNOWN, label, stmts);
	}

	public SwitchEntryStmt(Range range, final Optional<Expression> label,
	                       final NodeList<Statement> stmts) {
		super(range);
		setLabel(label);
		setStmts(stmts);
	}

	@Override
	public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Optional<Expression> getLabel() {
		return label;
	}

	@Override
    public NodeList<Statement> getStmts() {
        return stmts;
	}

	public SwitchEntryStmt setLabel(final Optional<Expression> label) {
		this.label = label;
		setAsParentNodeOf(this.label);
		return this;
	}

	@Override
    public SwitchEntryStmt setStmts(final NodeList<Statement> stmts) {
		this.stmts = assertNotNull(stmts);
		setAsParentNodeOf(this.stmts);
        return this;
	}
}
