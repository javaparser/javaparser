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

import static com.github.javaparser.Position.pos;
import static com.github.javaparser.utils.Utils.ensureNotNull;

import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithArrays;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class ReferenceType extends Type<ReferenceType> implements NodeWithType<ReferenceType>, NodeWithAnnotations<ReferenceType>, NodeWithArrays<ReferenceType>  {

	private Type type;

	private int arrayCount;

    private List<List<AnnotationExpr>> arraysAnnotations;

    public ReferenceType() {
	}

	public ReferenceType(final Type type) {
		setType(type);
	}

	public ReferenceType(final Type type, final int arrayCount) {
		setType(type);
		setArrayCount(arrayCount);
	}

	public ReferenceType(final Range range, final Type type, final int arrayCount) {
		super(range);
		setType(type);
		setArrayCount(arrayCount);
	}

    public ReferenceType(int beginLine, int beginColumn, int endLine,
                         int endColumn, Type type, int arrayCount,
                         List<AnnotationExpr> annotations,
                         List<List<AnnotationExpr>> arraysAnnotations) {
	    this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), type, arrayCount, annotations, arraysAnnotations);
    }
	
    public ReferenceType(Range range, Type type, int arrayCount,
                         List<AnnotationExpr> annotations,
                         List<List<AnnotationExpr>> arraysAnnotations) {
        super(range, annotations);
        setType(type);
        setArrayCount(arrayCount);
        this.arraysAnnotations = arraysAnnotations;
    }

	/**
	 * Creates a new {@link ReferenceType} for a class or interface.
	 *
	 * @param name
	 *            name of the class or interface
	 * @param arrayCount
	 *            number of arrays or <code>0</code> if is not a array.
	 * @return instanceof {@link ReferenceType}
	 */
	public static ReferenceType create(String name, int arrayCount) {
		return new ReferenceType(new ClassOrInterfaceType(name), arrayCount);
	}

	/**
	 * Creates a new {@link ReferenceType} for the given primitive type.
	 *
	 * @param type
	 *            primitive type
	 * @param arrayCount
	 *            number of arrays or <code>0</code> if is not a array.
	 * @return instanceof {@link ReferenceType}
	 */
	public static ReferenceType create(PrimitiveType type, int arrayCount) {
		return new ReferenceType(type, arrayCount);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	@Override
	public int getArrayCount() {
		return arrayCount;
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
	public ReferenceType setArrayCount(final int arrayCount) {
		this.arrayCount = arrayCount;
		return this;
	}

	@Override
    public ReferenceType setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
        return this;
	}

	@Override
    public List<List<AnnotationExpr>> getArraysAnnotations() {
        arraysAnnotations = ensureNotNull(arraysAnnotations);
        return arraysAnnotations;
    }

	@Override
    public ReferenceType setArraysAnnotations(List<List<AnnotationExpr>> arraysAnnotations) {
        this.arraysAnnotations = arraysAnnotations;
		return this;
    }
}
