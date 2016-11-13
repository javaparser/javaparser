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
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.utils.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class SwitchStmt extends Statement {

	private Expression selector;

	private List<SwitchEntryStmt> entriesList;

	public SwitchStmt() {
	}

	public SwitchStmt(final Expression selector,
			final List<SwitchEntryStmt> entriesList) {
		setSelector(selector);
		setEntriesList(entriesList);
	}

	public SwitchStmt(Range range, final Expression selector,
	                  final List<SwitchEntryStmt> entriesList) {
		super(range);
		setSelector(selector);
		setEntriesList(entriesList);
	}

	@Override
	public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<SwitchEntryStmt> getEntriesList() {
        entriesList = ensureNotNull(entriesList);
        return entriesList;
	}

	public Expression getSelector() {
		return selector;
	}

	public void setEntriesList(final List<SwitchEntryStmt> entriesList) {
		this.entriesList = entriesList;
		setAsParentNodeOf(this.entriesList);
	}

	public void setSelector(final Expression selector) {
		this.selector = selector;
		setAsParentNodeOf(this.selector);
	}
}
