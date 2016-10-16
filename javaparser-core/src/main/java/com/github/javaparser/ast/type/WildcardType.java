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
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.none;
import static com.github.javaparser.utils.Utils.some;

/**
 * @author Julio Vilmar Gesser
 */
public final class WildcardType extends Type<WildcardType> implements NodeWithAnnotations<WildcardType> {

	private Optional<ReferenceType<?>> ext;

	private Optional<ReferenceType<?>> sup;

	public WildcardType() {
        this(Range.UNKNOWN, none(), none());
	}

	public WildcardType(final ReferenceType<?> ext) {
		this(Range.UNKNOWN, some(ext), none());
	}

	public WildcardType(final Optional<ReferenceType<?>> ext, final Optional<ReferenceType<?>> sup) {
        this(Range.UNKNOWN, ext, sup);
	}

	public WildcardType(final Range range,
			final Optional<ReferenceType<?>> ext, final Optional<ReferenceType<?>> sup) {
		super(range, new NodeList<>());
		setExtends(ext);
		setSuper(sup);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Optional<ReferenceType<?>> getExtends() {
		return ext;
	}

	public Optional<ReferenceType<?>> getSuper() {
		return sup;
	}

	public WildcardType setExtends(final Optional<ReferenceType<?>> ext) {
		this.ext = assertNotNull(ext);
		setAsParentNodeOf(this.ext);
		return this;
	}

	public WildcardType setSuper(final Optional<ReferenceType<?>> sup) {
		this.sup = assertNotNull(sup);
		setAsParentNodeOf(this.sup);
		return this;
	}

}
