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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.TypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * Base class for types.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Type extends Node {

    private NodeList<AnnotationExpr> annotations;

    public Type(Range range, NodeList<AnnotationExpr> annotations) {
        super(range);
        setAnnotations(annotations);
    }

    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public AnnotationExpr getAnnotation(int i) {
        return getAnnotations().get(i);
    }

    public Type setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    /**
     * Finds the element type, meaning: the type without ArrayTypes around it.
     * <p>
     * In "<code>int[] a[];</code>", the element type is int.
     */
    public Type getElementType() {
        if (this instanceof ArrayType) {
            return ((ArrayType) this).getComponentType().getElementType();
        }
        return this;
    }

    public int getArrayLevel() {
        if (this instanceof ArrayType) {
            return 1 + ((ArrayType) this).getComponentType().getArrayLevel();
        } else {
            return 0;
        }
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public Type clone() {
        return (Type) accept(new CloneVisitor(), null);
    }

    @Override
    public TypeMetaModel getMetaModel() {
        return JavaParserMetaModel.typeMetaModel;
    }
}
