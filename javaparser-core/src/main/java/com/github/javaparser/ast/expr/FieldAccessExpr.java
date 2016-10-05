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
 
package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldAccessExpr extends Expression implements NodeWithTypeArguments<FieldAccessExpr> {

	private Expression scope;

	private List<Type<?>> typeArguments;

	private NameExpr field;

	public FieldAccessExpr() {
	}

	public FieldAccessExpr(final Expression scope, final String field) {
		setScope(scope);
		setField(field);
	}

	public FieldAccessExpr(final Range range, final Expression scope, final List<Type<?>> typeArguments, final String field) {
		super(range);
		setScope(scope);
		setTypeArguments(typeArguments);
		setField(field);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public String getField() {
		return field.getName();
	}

	public NameExpr getFieldExpr() {
		return field;
	}

	public Expression getScope() {
		return scope;
	}

	public FieldAccessExpr setField(final String field) {
		setFieldExpr(new NameExpr(field));
		return this;
	}

	public FieldAccessExpr setFieldExpr(NameExpr field) {
		this.field = field;
		setAsParentNodeOf(this.field);
		return this;
	}

	public FieldAccessExpr setScope(final Expression scope) {
		this.scope = scope;
		setAsParentNodeOf(this.scope);
		return this;
	}


	@Override
	public List<Type<?>> getTypeArguments() {
		return typeArguments;
	}

	@Override
	public FieldAccessExpr setTypeArguments(final List<Type<?>> types) {
		this.typeArguments = types;
		setAsParentNodeOf(this.typeArguments);
		return this;
	}
}
