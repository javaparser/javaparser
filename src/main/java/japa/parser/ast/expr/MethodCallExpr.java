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
package japa.parser.ast.expr;

import japa.parser.ast.type.Type;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

import java.util.Iterator;
import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodCallExpr extends Expression {

	private Expression scope;

	private List<Type> typeArgs;

	private String name;

	private List<Expression> args;

	public MethodCallExpr() {
	}

	public MethodCallExpr(final Expression scope, final String name) {
		setScope(scope);
		setName(name);
	}

	public MethodCallExpr(final Expression scope, final String name, final List<Expression> args) {
		setScope(scope);
		setName(name);
		setArgs(args);
	}

	public MethodCallExpr(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final Expression scope, final List<Type> typeArgs, final String name, final List<Expression> args) {
		super(beginLine, beginColumn, endLine, endColumn);
		setScope(scope);
		setTypeArgs(typeArgs);
		setName(name);
		setArgs(args);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<Expression> getArgs() {
		return args;
	}

	public String getName() {
		return name;
	}

	public Expression getScope() {
		return scope;
	}

	public List<Type> getTypeArgs() {
		return typeArgs;
	}

	public void setArgs(final List<Expression> args) {
		this.args = args;
		if(this.args != null){
			Iterator<Expression> it = args.iterator();
			while(it.hasNext()){
				it.next().setParentNode(this);
			}
		}
	}

	public void setName(final String name) {
		this.name = name;
	}

	public void setScope(final Expression scope) {
		this.scope = scope;
		if(this.scope!=null){
			this.scope.setParentNode(this);
		}
	}

	public void setTypeArgs(final List<Type> typeArgs) {
		this.typeArgs = typeArgs;
		if(this.typeArgs!=null){
			Iterator<Type> it = this.typeArgs.iterator();
			while(it.hasNext()){
				it.next().setParentNode(this);
			}
		}
	}

}
