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

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

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
public final class TypeParameter extends ReferenceType<TypeParameter> implements NodeWithName<TypeParameter> {

	private String name;

    private NodeList<AnnotationExpr> annotations;

	private NodeList<ClassOrInterfaceType> typeBound;

	public TypeParameter() {
		this(Range.UNKNOWN,
				"",
				new NodeList<>(),
				new NodeList<>());
	}

	public TypeParameter(final String name, final NodeList<ClassOrInterfaceType> typeBound) {
		this(Range.UNKNOWN,
				name,
				typeBound,
				new NodeList<>());
	}

	public TypeParameter(Range range, final String name, final NodeList<ClassOrInterfaceType> typeBound) {
		this(range,
				name,
				typeBound,
				new NodeList<>());
	}

	public TypeParameter(Range range, String name, NodeList<ClassOrInterfaceType> typeBound, NodeList<AnnotationExpr> annotations) {
		super(range);
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
	@Override
	public String getName() {
		return name;
	}

	/**
	 * Return the list of {@link ClassOrInterfaceType} that this parameter
	 * extends. Return <code>null</code> null if there are no type.
	 * 
	 * @return list of types that this paramente extends or <code>null</code>
	 */
	public NodeList<ClassOrInterfaceType> getTypeBound() {
        return typeBound;
	}

    @Override
    public TypeParameter setName(final String name) {
		this.name = name;
        return this;
	}

	public TypeParameter setTypeBound(final NodeList<ClassOrInterfaceType> typeBound) {
		this.typeBound = assertNotNull(typeBound);
		setAsParentNodeOf(typeBound);
		return this;
	}

	@Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

	@Override
    public TypeParameter setAnnotations(NodeList<AnnotationExpr> annotations) {
		this.annotations = assertNotNull(annotations);
	    setAsParentNodeOf(this.annotations);
		return this;
    }
}
