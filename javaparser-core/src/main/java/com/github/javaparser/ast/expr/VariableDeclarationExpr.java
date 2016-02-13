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

import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Collections;
import java.util.List;

import static com.github.javaparser.ast.internal.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarationExpr extends Expression implements TypedNode {

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
        annotations = ensureNotNull(annotations);
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

	@Override
	public Type getType() {
		return type;
	}

	public List<VariableDeclarator> getVars() {
        vars = ensureNotNull(vars);
        return vars;
	}

	public void setAnnotations(final List<AnnotationExpr> annotations) {
        this.annotations = annotations;
		setAsParentNodeOf(this.annotations);
	}

	public void setModifiers(final int modifiers) {
		this.modifiers = modifiers;
	}

	@Override
	public void setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
	}

	public void setVars(final List<VariableDeclarator> vars) {
		this.vars = vars;
		setAsParentNodeOf(this.vars);
	}
}
