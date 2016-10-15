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
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.ast.expr.NameExpr.name;
import static com.github.javaparser.utils.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class SwitchStmt extends Statement {

	private Expression selector;

	private NodeList<SwitchEntryStmt> entries;

	public SwitchStmt() {
		this(Range.UNKNOWN, new NameExpr(), new NodeList<>());
	}

	public SwitchStmt(final Expression selector,
			final NodeList<SwitchEntryStmt> entries) {
		this(Range.UNKNOWN, selector, entries);
	}

	public SwitchStmt(Range range, final Expression selector,
	                  final NodeList<SwitchEntryStmt> entries) {
		super(range);
		setSelector(selector);
		setEntries(entries);
	}

	@Override
	public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public NodeList<SwitchEntryStmt> getEntries() {
        return entries;
	}

	public Expression getSelector() {
		return selector;
	}

	public SwitchStmt setEntries(final NodeList<SwitchEntryStmt> entries) {
		this.entries = assertNotNull(entries);
		setAsParentNodeOf(this.entries);
		return this;
	}

	public SwitchStmt setSelector(final Expression selector) {
		this.selector = selector;
		setAsParentNodeOf(this.selector);
		return this;
	}
}
