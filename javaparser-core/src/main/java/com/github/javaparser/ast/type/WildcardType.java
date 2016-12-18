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
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

/**
 * @author Julio Vilmar Gesser
 */
public final class WildcardType extends Type implements NodeWithAnnotations<WildcardType> {

    private ReferenceType extendedTypes;

    private ReferenceType superTypes;

    public WildcardType() {
        this(null, null, null);
    }

    public WildcardType(final ReferenceType extendedTypes) {
        this(null, extendedTypes, null);
    }

    public WildcardType(final ReferenceType extendedTypes, final ReferenceType superTypes) {
        this(null, extendedTypes, superTypes);
    }

    public WildcardType(final Range range,
                        final ReferenceType extendedTypes, final ReferenceType superTypes) {
        super(range, new NodeList<>());
        setExtendedTypes(extendedTypes);
        setSuperTypes(superTypes);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Optional<ReferenceType> getExtendedTypes() {
        return Optional.ofNullable(extendedTypes);
    }

    public Optional<ReferenceType> getSuperTypes() {
        return Optional.ofNullable(superTypes);
    }

    /**
     * Sets the extends
     *
     * @param ext the extends, can be null
     * @return this, the WildcardType
     */
    public WildcardType setExtendedTypes(final ReferenceType ext) {
        notifyPropertyChange(ObservableProperty.EXTENDED_TYPES, this.extendedTypes, ext);
        this.extendedTypes = ext;
        setAsParentNodeOf(this.extendedTypes);
        return this;
    }

    /**
     * Sets the super
     *
     * @param sup the super, can be null
     * @return this, the WildcardType
     */
    public WildcardType setSuperTypes(final ReferenceType sup) {
        notifyPropertyChange(ObservableProperty.SUPER, this.superTypes, sup);
        this.superTypes = sup;
        setAsParentNodeOf(this.superTypes);
        return this;
    }

    @Override
    public WildcardType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (WildcardType) super.setAnnotations(annotations);
    }
}
