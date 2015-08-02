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

package com.github.javaparser.ast.type;

import com.github.javaparser.ast.NamedNode;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceType extends Type {

	private ClassOrInterfaceType scope;

	private String name;

	private List<Type> typeArgs;

	public ClassOrInterfaceType() {
	}

	public ClassOrInterfaceType(final String name) {
		setName(name);
	}

	public ClassOrInterfaceType(final ClassOrInterfaceType scope, final String name) {
		setScope(scope);
		setName(name);
	}

	public ClassOrInterfaceType(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final ClassOrInterfaceType scope, final String name, final List<Type> typeArgs) {
		super(beginLine, beginColumn, endLine, endColumn);
		setScope(scope);
		setName(name);
		setTypeArgs(typeArgs);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public String getName() {
		return name;
	}

	public ClassOrInterfaceType getScope() {
		return scope;
	}

	public List<Type> getTypeArgs() {
		return typeArgs;
	}

	public boolean isBoxedType() {
		return PrimitiveType.Primitive.unboxMap.containsKey(name);
	}

	public PrimitiveType toUnboxedType() throws UnsupportedOperationException {
		if(!isBoxedType())
			throw new UnsupportedOperationException(name + " isn't a boxed type.");
		return new PrimitiveType(PrimitiveType.Primitive.unboxMap.get(name));
	}

	public void setName(final String name) {
		this.name = name;
	}

	public void setScope(final ClassOrInterfaceType scope) {
		this.scope = scope;
		setAsParentNodeOf(this.scope);
	}

	public void setTypeArgs(final List<Type> typeArgs) {
		this.typeArgs = typeArgs;
		setAsParentNodeOf(this.typeArgs);
	}
}
