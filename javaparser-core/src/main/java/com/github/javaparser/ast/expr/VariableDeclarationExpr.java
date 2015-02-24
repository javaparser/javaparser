/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.body.ModifierUtils;
import com.github.javaparser.ast.body.ModifiersSet;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import javax.lang.model.element.Modifier;
import java.util.List;
import java.util.Set;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarationExpr extends Expression implements NodeWithModifiers {

	private ModifiersSet modifiers = new ModifiersSet();

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
	 * Return the modifiers of this member declaration.
	 *
	 * @see com.github.javaparser.ast.body.ModifierUtils
	 * @return modifiers
	 * @deprecated please use getModifiersSet instead
	 */
	@Override
	@Deprecated
	public int getModifiers() {
		return ModifierUtils.toInt(modifiers);
	}

	/**
	 * Return the modifiers of this member declaration.
	 *
	 * @see com.github.javaparser.ast.body.ModifierUtils
	 * @return modifiers
	 */
	@Override
	public ModifiersSet getModifiersSet() {
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

	public final void setModifiers(ModifiersSet modifiers) {
		this.modifiers = modifiers;
	}

	public final void setModifiers(int modifiers) {
		this.modifiers = ModifierUtils.toSet(modifiers);
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
