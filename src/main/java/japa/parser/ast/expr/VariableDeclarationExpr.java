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
 * Created on 03/11/2006
 */
package japa.parser.ast.expr;

import japa.parser.ast.body.ModifierSet;
import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.type.Type;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarationExpr extends Expression {

	private int modifiers;

	private List<AnnotationExpr> annotations;

	private Type type;

	private List<VariableDeclarator> vars;

	public VariableDeclarationExpr() {
	}

	public VariableDeclarationExpr(final Type type, final List<VariableDeclarator> vars) {
		setType(type);
		setVars(vars);
	}

	public VariableDeclarationExpr(final int modifiers, final Type type, final List<VariableDeclarator> vars) {
		setModifiers(modifiers);
		setType(type);
		setVars(vars);
	}

	public VariableDeclarationExpr(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final int modifiers, final List<AnnotationExpr> annotations, final Type type,
			final List<VariableDeclarator> vars) {
		super(beginLine, beginColumn, endLine, endColumn);
		setModifiers(modifiers);
		setAnnotations(annotations);
		setType(type);
		setVars(vars);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<AnnotationExpr> getAnnotations() {
		return annotations;
	}

	/**
	 * Return the modifiers of this variable declaration.
	 * 
	 * @see ModifierSet
	 * @return modifiers
	 */
	public int getModifiers() {
		return modifiers;
	}

	public Type getType() {
		return type;
	}

	public List<VariableDeclarator> getVars() {
		return vars;
	}

	public void setAnnotations(final List<AnnotationExpr> annotations) {
		this.annotations = annotations;
		setAsParentNodeOf(this.annotations);
	}

	public void setModifiers(final int modifiers) {
		this.modifiers = modifiers;
	}

	public void setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
	}

	public void setVars(final List<VariableDeclarator> vars) {
		this.vars = vars;
		setAsParentNodeOf(this.vars);
	}
}
