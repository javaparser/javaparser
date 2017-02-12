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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.WildcardTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A wildcard type argument.
 * <br/><code>void printCollection(Collection&lt;<b>?</b>> c) { ... }</code>
 * <br/><code>boolean addAll(Collection&lt;<b>? extends E</b>> c)</code>
 * <br/><code>Reference(T referent, ReferenceQueue&lt;<b>? super T</b>> queue)</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class WildcardType extends Type implements NodeWithAnnotations<WildcardType> {

    private ReferenceType extendedType;

    private ReferenceType superType;

    public WildcardType() {
        this(null, null, null);
    }

    public WildcardType(final ReferenceType extendedType) {
        this(null, extendedType, null);
    }

    @AllFieldsConstructor
    public WildcardType(final ReferenceType extendedType, final ReferenceType superType) {
        this(null, extendedType, superType);
    }

    public WildcardType(final Range range, final ReferenceType extendedType, final ReferenceType superType) {
        super(range, new NodeList<>());
        setExtendedType(extendedType);
        setSuperType(superType);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Optional<ReferenceType> getExtendedType() {
        return Optional.ofNullable(extendedType);
    }

    public Optional<ReferenceType> getSuperType() {
        return Optional.ofNullable(superType);
    }

    /**
     * Sets the extends
     *
     * @param ext the extends, can be null
     * @return this, the WildcardType
     */
    public WildcardType setExtendedType(final ReferenceType extendedType) {
        notifyPropertyChange(ObservableProperty.EXTENDED_TYPES, this.extendedType, extendedType);
        if (this.extendedType != null)
            this.extendedType.setParentNode(null);
        this.extendedType = extendedType;
        setAsParentNodeOf(extendedType);
        return this;
    }

    /**
     * Sets the super
     *
     * @param sup the super, can be null
     * @return this, the WildcardType
     */
    public WildcardType setSuperType(final ReferenceType superType) {
        notifyPropertyChange(ObservableProperty.SUPER_TYPES, this.superType, superType);
        if (this.superType != null)
            this.superType.setParentNode(null);
        this.superType = superType;
        setAsParentNodeOf(superType);
        return this;
    }

    @Override
    public WildcardType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (WildcardType) super.setAnnotations(annotations);
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (extendedType != null) {
            if (node == extendedType) {
                removeExtendedTypes();
                return true;
            }
        }
        if (superType != null) {
            if (node == superType) {
                removeSuperTypes();
                return true;
            }
        }
        return super.remove(node);
    }

    public WildcardType removeExtendedTypes() {
        return setExtendedType((ReferenceType) null);
    }

    public WildcardType removeSuperTypes() {
        return setSuperType((ReferenceType) null);
    }

    @Override
    public WildcardType clone() {
        return (WildcardType) accept(new CloneVisitor(), null);
    }

    @Override
    public WildcardTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.wildcardTypeMetaModel;
    }
}

