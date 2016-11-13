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
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.utils.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodCallExpr extends Expression {

	private Expression scope;

	private List<Type> typeArgsList;

	private NameExpr name;

	private List<Expression> argsList;

	public MethodCallExpr() {
	}

	public MethodCallExpr(final Expression scope, final String name) {
		setScope(scope);
		setName(name);
	}

	public MethodCallExpr(final Expression scope, final String name, final List<Expression> argsList) {
		setScope(scope);
		setName(name);
		setArgsList(argsList);
	}

	public MethodCallExpr(final Range range, final Expression scope, final List<Type> typeArgsList, final String name, final List<Expression> argsList) {
		super(range);
		setScope(scope);
		setTypeArgsList(typeArgsList);
		setName(name);
		setArgsList(argsList);
	}


	/**
	 * Adds the given argument to the method call. The list of arguments will be
	 * initialized if it is <code>null</code>.
	 *
	 * @param arg
	 *            argument value
	 */
	public MethodCallExpr addArgument(Expression arg) {
		List<Expression> args = getArgsList();
		if (isNullOrEmpty(args)) {
			args = new ArrayList<>();
			setArgsList(args);
		}
		args.add(arg);
		arg.setParentNode(this);
		return this;
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<Expression> getArgsList() {
        argsList = ensureNotNull(argsList);
        return argsList;
	}

	public String getName() {
		return name.getName();
	}

	public NameExpr getNameExpr() {
		return name;
	}

	public Expression getScope() {
		return scope;
	}

	public List<Type> getTypeArgsList() {
        typeArgsList = ensureNotNull(typeArgsList);
        return typeArgsList;
	}

	public void setArgsList(final List<Expression> argsList) {
		this.argsList = argsList;
		setAsParentNodeOf(this.argsList);
	}

	public void setName(final String name) {
		setNameExpr(new NameExpr(name));
	}

	public void setNameExpr(NameExpr name) {
		this.name = name;
		setAsParentNodeOf(this.name);
	}

	public void setScope(final Expression scope) {
		this.scope = scope;
		setAsParentNodeOf(this.scope);
	}

	public void setTypeArgsList(final List<Type> typeArgsList) {
		this.typeArgsList = typeArgsList;
		setAsParentNodeOf(this.typeArgsList);
	}
}
