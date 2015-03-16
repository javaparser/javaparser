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

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.lexical.Comment;
import com.github.javaparser.ast.lexical.CommentAttributes;
import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceDeclaration extends TypeDeclaration implements DocumentableNode {

	private boolean interface_;

	private List<TypeParameter> typeParameters;

	// Can contain more than one item if this is an interface
	private List<ClassOrInterfaceType> extendsList;

	private List<ClassOrInterfaceType> implementsList;

	public ClassOrInterfaceDeclaration() {
	}

	public ClassOrInterfaceDeclaration(final int modifiers, final boolean isInterface, final String name) {
		super(modifiers, name);
		setInterface(isInterface);
	}

	public ClassOrInterfaceDeclaration(final int modifiers,
			final List<AnnotationExpr> annotations, final boolean isInterface, final String name,
			final List<TypeParameter> typeParameters, final List<ClassOrInterfaceType> extendsList,
			final List<ClassOrInterfaceType> implementsList, final List<BodyDeclaration> members) {
		super(annotations, modifiers, name, members);
		setInterface(isInterface);
		setTypeParameters(typeParameters);
		setExtends(extendsList);
		setImplements(implementsList);
	}

	public ClassOrInterfaceDeclaration(Lexeme first, Lexeme last, final int modifiers,
			final List<AnnotationExpr> annotations, final boolean isInterface, final String name,
			final List<TypeParameter> typeParameters, final List<ClassOrInterfaceType> extendsList,
			final List<ClassOrInterfaceType> implementsList, final List<BodyDeclaration> members) {
		super(first, last, annotations, modifiers, name, members);
		setInterface(isInterface);
		setTypeParameters(typeParameters);
		setExtends(extendsList);
		setImplements(implementsList);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<ClassOrInterfaceType> getExtends() {
		return extendsList;
	}

	public List<ClassOrInterfaceType> getImplements() {
		return implementsList;
	}

	public List<TypeParameter> getTypeParameters() {
		return typeParameters;
	}

    public boolean isInterface() {
		return interface_;
	}

	public void setExtends(final List<ClassOrInterfaceType> extendsList) {
		this.extendsList = extendsList;
		setAsParentNodeOf(this.extendsList);
	}

	public void setImplements(final List<ClassOrInterfaceType> implementsList) {
		this.implementsList = implementsList;
		setAsParentNodeOf(this.implementsList);
	}

	public void setInterface(final boolean interface_) {
		this.interface_ = interface_;
	}

	public void setTypeParameters(final List<TypeParameter> typeParameters) {
		this.typeParameters = typeParameters;
		setAsParentNodeOf(this.typeParameters);
	}

    @Override
    public void setJavaDoc(Comment javadoc) {
        CommentAttributes comments = getCommentAttributes();
        if (comments == null) {
            comments = new CommentAttributes();
            setCommentAttributes(comments);
        }
        comments.setJavadocComment(javadoc);
    }

    @Override
    public Comment getJavaDoc() {
        return getCommentAttributes().getJavadocComment();
    }
}
