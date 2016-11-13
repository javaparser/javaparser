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
 
package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class InstanceOfExpr extends Expression implements NodeWithType<InstanceOfExpr, ReferenceType<?>> {

	private Expression expr;

	private ReferenceType<?> type;

	public InstanceOfExpr() {
        this(Range.UNKNOWN, new NameExpr(), new ClassOrInterfaceType());
	}

	public InstanceOfExpr(final Expression expr, final ReferenceType<?> type) {
        this(Range.UNKNOWN, expr, type);
	}

	public InstanceOfExpr(final Range range, final Expression expr, final ReferenceType<?> type) {
		super(range);
		setExpr(expr);
		setType(type);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Expression getExpr() {
		return expr;
	}

	@Override
	public ReferenceType<?> getType() {
		return type;
	}

	public InstanceOfExpr setExpr(final Expression expr) {
		notifyPropertyChange(ObservableProperty.EXPR, this.expr, expr);
		this.expr = assertNotNull(expr);
		setAsParentNodeOf(this.expr);
		return this;
	}

	@Override
    public InstanceOfExpr setType(final ReferenceType<?> type) {
		notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
		this.type = assertNotNull(type);
		setAsParentNodeOf(this.type);
        return this;
	}
}
