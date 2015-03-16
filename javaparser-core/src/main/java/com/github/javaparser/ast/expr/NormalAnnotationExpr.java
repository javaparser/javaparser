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

import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class NormalAnnotationExpr extends AnnotationExpr {

	private List<MemberValuePair> pairs;

	public NormalAnnotationExpr() {
	}

	public NormalAnnotationExpr(final NameExpr name, final List<MemberValuePair> pairs) {
		setName(name);
		setPairs(pairs);
	}

	public NormalAnnotationExpr(Lexeme first, Lexeme last,
			final NameExpr name, final List<MemberValuePair> pairs) {
		super(first, last);
		setName(name);
		setPairs(pairs);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<MemberValuePair> getPairs() {
		return pairs;
	}

	public void setPairs(final List<MemberValuePair> pairs) {
		this.pairs = pairs;
		setAsParentNodeOf(this.pairs);
	}
}
