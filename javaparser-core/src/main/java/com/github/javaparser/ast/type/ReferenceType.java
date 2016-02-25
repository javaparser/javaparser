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
 
package com.github.javaparser.ast.type;

import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.ast.internal.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class ReferenceType extends Type implements TypedNode {

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

	public ReferenceType(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final Type type, final int arrayCount) {
		super(beginLine, beginColumn, endLine, endColumn);
		setType(type);
		setArrayCount(arrayCount);
	}

    public ReferenceType(int beginLine, int beginColumn, int endLine,
                         int endColumn, Type type, int arrayCount,
                         List<AnnotationExpr> annotations,
                         List<List<AnnotationExpr>> arraysAnnotations) {
        super(beginLine, beginColumn, endLine, endColumn, annotations);
        setType(type);
        setArrayCount(arrayCount);
        this.arraysAnnotations = arraysAnnotations;
    }

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public int getArrayCount() {
		return arrayCount;
	}

	@Override
	public Type getType() {
		return type;
	}

	public void setArrayCount(final int arrayCount) {
		this.arrayCount = arrayCount;
	}

	@Override
	public void setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
	}

	/**
	 * <p>Arrays annotations are annotations on the arrays modifiers of the type.
	 * Consider this example:</p>
	 * 
	 * <p><pre>
	 * {@code
	 * int @Ann1 [] @Ann2 [] array;
	 * }</pre></p>
	 * 
	 * <p>in this this method will return a list with the annotation expressions <pre>@Ann1</pre>
	 * and <pre>@Ann2</pre></p>
	 * 
	 * <p>Note that the first list element of arraysAnnotations will refer to the first array modifier encountered.
	 * Considering the example the first element will be a list containing just @Ann1 while the second element will
	 * be a list containing just @Ann2.
	 * </p>
	 *
	 * <p>This property is guaranteed to hold: <pre>{@code getArraysAnnotations().size() == getArrayCount()}</pre>
	 * If a certain array modifier has no annotation the corresponding entry of arraysAnnotations will be null</p>
	 */
    public List<List<AnnotationExpr>> getArraysAnnotations() {
        arraysAnnotations = ensureNotNull(arraysAnnotations);
        return arraysAnnotations;
    }

	/**
	 * For a description of the arrayAnnotations field refer to {@link #getArraysAnnotations()}
	 */
    public void setArraysAnnotations(List<List<AnnotationExpr>> arraysAnnotations) {
        this.arraysAnnotations = arraysAnnotations;
    }
}
