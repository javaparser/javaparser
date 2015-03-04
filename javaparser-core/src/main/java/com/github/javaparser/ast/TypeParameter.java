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
package com.github.javaparser.ast;

import com.github.javaparser.Position;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * <p>
 * This class represents the declaration of a generics argument.
 * </p>
 * The TypeParameter is constructed following the syntax:<br>
 * <pre>
 * {@code
 * TypeParameter ::= <IDENTIFIER> ( "extends" }{@link ClassOrInterfaceType}{@code ( "&" }{@link ClassOrInterfaceType}{@code )* )?
 * }
 * </pre>
 * @author Julio Vilmar Gesser
 */
public final class TypeParameter extends Node {

	private String name;

    private List<AnnotationExpr> annotations;

	private List<ClassOrInterfaceType> typeBound;

	public TypeParameter() {
	}

	public TypeParameter(final String name, final List<ClassOrInterfaceType> typeBound) {
		setName(name);
		setTypeBound(typeBound);
	}

	public TypeParameter(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final String name, final List<ClassOrInterfaceType> typeBound) {
		super(beginLine, beginColumn, endLine, endColumn);
		setName(name);
		setTypeBound(typeBound);
	}

    public TypeParameter(int beginLine, int beginColumn, int endLine,
                         int endColumn, String name, List<ClassOrInterfaceType> typeBound, List<AnnotationExpr> annotations) {
        this(beginLine, beginColumn, endLine, endColumn, name, typeBound);
        setName(name);
        setTypeBound(typeBound);
	    setAnnotations(annotations);
    }

	public TypeParameter(Position begin, Position end,
			final String name, final List<ClassOrInterfaceType> typeBound) {
		super(begin, end);
		setName(name);
		setTypeBound(typeBound);
	}

	public TypeParameter(Position begin, Position end,
			final String name, final List<ClassOrInterfaceType> typeBound, final List<AnnotationExpr> annotations) {
		super(begin, end);
		setName(name);
		setTypeBound(typeBound);
		setAnnotations(annotations);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	/**
	 * Return the name of the paramenter.
	 * 
	 * @return the name of the paramenter
	 */
	public String getName() {
		return name;
	}

	/**
	 * Return the list of {@link ClassOrInterfaceType} that this parameter
	 * extends. Return <code>null</code> null if there are no type.
	 * 
	 * @return list of types that this paramente extends or <code>null</code>
	 */
	public List<ClassOrInterfaceType> getTypeBound() {
		return typeBound;
	}

	/**
	 * Sets the name of this type parameter.
	 * 
	 * @param name
	 *            the name to set
	 */
	public void setName(final String name) {
		this.name = name;
	}

	/**
	 * Sets the list o types.
	 * 
	 * @param typeBound
	 *            the typeBound to set
	 */
	public void setTypeBound(final List<ClassOrInterfaceType> typeBound) {
		this.typeBound = typeBound;
		setAsParentNodeOf(typeBound);
	}

    public List<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public void setAnnotations(List<AnnotationExpr> annotations) {
        this.annotations = annotations;
	    setAsParentNodeOf(annotations);
    }
}
