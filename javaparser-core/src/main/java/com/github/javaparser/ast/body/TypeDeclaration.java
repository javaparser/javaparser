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
 
package com.github.javaparser.ast.body;

import static com.github.javaparser.Position.pos;
import static com.github.javaparser.ast.internal.Utils.ensureNotNull;

import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.NamedNode;
import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class TypeDeclaration<T> extends BodyDeclaration<T>
        implements NamedNode<T>, DocumentableNode<T>, NodeWithModifiers<T> {

	private NameExpr name;

	private int modifiers;

    private List<BodyDeclaration<?>> members;

	public TypeDeclaration() {
	}

	public TypeDeclaration(int modifiers, String name) {
		setName(name);
		setModifiers(modifiers);
	}

	public TypeDeclaration(List<AnnotationExpr> annotations,
			int modifiers, String name,
                           List<BodyDeclaration<?>> members) {
		super(annotations);
		setName(name);
		setModifiers(modifiers);
		setMembers(members);
	}

	/**
	 * @deprecated prefer using Range objects.
	 */
	@Deprecated
	public TypeDeclaration(int beginLine, int beginColumn, int endLine,
			int endColumn, List<AnnotationExpr> annotations,
			int modifiers, String name,
                           List<BodyDeclaration<?>> members) {
		this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), annotations, modifiers, name, members);
	}
	
	public TypeDeclaration(Range range, List<AnnotationExpr> annotations,
			int modifiers, String name,
                           List<BodyDeclaration<?>> members) {
		super(range, annotations);
		setName(name);
		setModifiers(modifiers);
		setMembers(members);
	}

    public final List<BodyDeclaration<?>> getMembers() {
        	members = ensureNotNull(members);
        	return members;
	}

	/**
	 * Return the modifiers of this type declaration.
	 * 
	 * @see ModifierSet
	 * @return modifiers
	 */
	@Override
	public final int getModifiers() {
		return modifiers;
	}

	@Override
	public final String getName() {
		return name.getName();
	}

    public void setMembers(List<BodyDeclaration<?>> members) {
		this.members = members;
		setAsParentNodeOf(this.members);
	}

	public final void setModifiers(int modifiers) {
		this.modifiers = modifiers;
	}

	public final void setName(String name) {
		setNameExpr(new NameExpr(name));
	}

	public final void setNameExpr(NameExpr nameExpr) {
		this.name = nameExpr;
		setAsParentNodeOf(this.name);
	}

	public final NameExpr getNameExpr() {
		return name;
	}

	@Override
	public JavadocComment getJavaDoc() {
		if(getComment() instanceof JavadocComment){
			return (JavadocComment) getComment();
		}
		return null;
	}

}
