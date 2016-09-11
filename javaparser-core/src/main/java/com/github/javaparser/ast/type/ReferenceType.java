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
 
package com.github.javaparser.ast.type;

import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public class ReferenceType extends Type<ReferenceType> implements NodeWithType<ReferenceType>, NodeWithAnnotations<ReferenceType> {

	private Type type;

    public ReferenceType() {
	}

	public ReferenceType(final Type type) {
		setType(type);
	}

	public ReferenceType(final Range range, final Type type) {
		super(range);
		setType(type);
	}

    public ReferenceType(Range range, Type type, List<AnnotationExpr> annotations) {
        super(range, annotations);
        setType(type);
    }

	/**
	 * Creates a new {@link ReferenceType} for a class or interface.
	 *
	 * @param name
	 *            name of the class or interface
	 * @return instanceof {@link ReferenceType}
	 */
	public static ReferenceType create(String name) {
		return new ReferenceType(new ClassOrInterfaceType(name));
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
    public ReferenceType setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
        return this;
	}
}
