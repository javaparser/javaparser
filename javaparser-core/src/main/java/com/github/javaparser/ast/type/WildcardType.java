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

import java.util.Optional;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class WildcardType extends Type<WildcardType> implements NodeWithAnnotations<WildcardType> {

    private ReferenceType<?> ext;

    private ReferenceType<?> sup;

	public WildcardType() {
        this(Range.UNKNOWN, null, null);
	}

	public WildcardType(final ReferenceType<?> ext) {
		this(Range.UNKNOWN, ext, null);
	}

	public WildcardType(final ReferenceType<?> ext, final ReferenceType<?> sup) {
        this(Range.UNKNOWN, ext, sup);
	}

	public WildcardType(final Range range,
			final ReferenceType<?> ext, final ReferenceType<?> sup) {
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
        return Optional.ofNullable(ext);
	}

    public Optional<ReferenceType<?>> getSuper() {
        return Optional.ofNullable(sup);
	}

    /**
     * Sets the extends
     * 
     * @param ext the extends, can be null
     * @return this, the WildcardType
     */
    public WildcardType setExtends(final ReferenceType<?> ext) {
		this.ext = ext;
		setAsParentNodeOf(this.ext);
		return this;
	}

    /**
     * Sets the super
     * 
     * @param sup the super, can be null
     * @return this, the WildcardType
     */
    public WildcardType setSuper(final ReferenceType<?> sup) {
		this.sup = sup;
		setAsParentNodeOf(this.sup);
		return this;
	}

}
