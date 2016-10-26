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
 
package com.github.javaparser.ast.body;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithName;

import java.util.EnumSet;

import static com.github.javaparser.ast.expr.NameExpr.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class TypeDeclaration<T> extends BodyDeclaration<T>
        implements NodeWithName<T>, NodeWithJavaDoc<T>, NodeWithModifiers<T>, NodeWithMembers<T> {

	private NameExpr name;

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private NodeList<BodyDeclaration<?>> members;

	public TypeDeclaration() {
		this(Range.UNKNOWN,
                new NodeList<>(),
                EnumSet.noneOf(Modifier.class),
                new NameExpr(),
                new NodeList<>());
	}

    public TypeDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(Range.UNKNOWN,
                new NodeList<>(),
                modifiers,
                name(name),
                new NodeList<>());
	}

	public TypeDeclaration(NodeList<AnnotationExpr> annotations,
                           EnumSet<Modifier> modifiers, NameExpr name,
                           NodeList<BodyDeclaration<?>> members) {
        this(Range.UNKNOWN,
                annotations,
                modifiers,
                name,
                members);
	}

	public TypeDeclaration(Range range, NodeList<AnnotationExpr> annotations,
                           EnumSet<Modifier> modifiers, NameExpr name,
                           NodeList<BodyDeclaration<?>> members) {
		super(range, annotations);
		setNameExpr(name);
		setModifiers(modifiers);
		setMembers(members);
	}

	/**
	 * Adds the given declaration to the specified type.
	 *
	 * @param decl
	 *            member declaration
	 */
	public TypeDeclaration<T> addMember(BodyDeclaration<?> decl) {
		NodeList<BodyDeclaration<?>> members = getMembers();
		members.add(decl);
		return this;
	}

	@Override
	public NodeList<BodyDeclaration<?>> getMembers() {
		return members;
	}

	/**
     * Return the modifiers of this type declaration.
     * 
     * @see Modifier
     * @return modifiers
     */
	@Override
    public final EnumSet<Modifier> getModifiers() {
		return modifiers;
	}

	@Override
	public final String getName() {
		return name.getName();
	}

    @SuppressWarnings("unchecked")
    @Override
    public T setMembers(NodeList<BodyDeclaration<?>> members) {
		this.members = assertNotNull(members);
		setAsParentNodeOf(this.members);
        return (T) this;
	}

    @SuppressWarnings("unchecked")
    @Override
    public T setModifiers(EnumSet<Modifier> modifiers) {
		this.modifiers = assertNotNull(modifiers);
        return (T) this;
	}

    @Override
    @SuppressWarnings("unchecked")
    public T setName(String name) {
		setNameExpr(new NameExpr(assertNotNull(name)));
        return (T) this;
	}

    @SuppressWarnings("unchecked")
    public T setNameExpr(NameExpr nameExpr) {
		this.name = assertNotNull(nameExpr);
		setAsParentNodeOf(name);
        return (T) this;
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
