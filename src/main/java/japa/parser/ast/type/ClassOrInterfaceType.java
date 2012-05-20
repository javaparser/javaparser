/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 05/10/2006
 */
package japa.parser.ast.type;

import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

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
