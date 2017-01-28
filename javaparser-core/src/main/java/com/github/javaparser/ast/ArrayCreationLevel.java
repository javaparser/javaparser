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
package com.github.javaparser.ast;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * In <code>new int[1][2];</code> there are two ArrayCreationLevel objects,
 * the first one contains the expression "1",
 * the second the expression "2".
 */
public class ArrayCreationLevel extends Node implements NodeWithAnnotations<ArrayCreationLevel> {

    private Expression dimension;

    private NodeList<AnnotationExpr> annotations = new NodeList<>();

    public ArrayCreationLevel() {
        this(null, null, new NodeList<>());
    }

    public ArrayCreationLevel(int dimension) {
        this(null, new IntegerLiteralExpr("" + dimension), new NodeList<>());
    }

    public ArrayCreationLevel(Expression dimension) {
        this(null, dimension, new NodeList<>());
    }

    @AllFieldsConstructor
    public ArrayCreationLevel(Expression dimension, NodeList<AnnotationExpr> annotations) {
        this(null, dimension, annotations);
    }

    public ArrayCreationLevel(Range range, Expression dimension, NodeList<AnnotationExpr> annotations) {
        super(range);
        setDimension(dimension);
        setAnnotations(annotations);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * Sets the dimension
     *
     * @param dimension the dimension, can be null
     * @return this, the ArrayCreationLevel
     */
    public ArrayCreationLevel setDimension(Expression dimension) {
        notifyPropertyChange(ObservableProperty.DIMENSION, this.dimension, dimension);
        this.dimension = dimension;
        setAsParentNodeOf(dimension);
        return this;
    }

    public Optional<Expression> getDimension() {
        return Optional.ofNullable(dimension);
    }

    @Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    @Override
    public ArrayCreationLevel setAnnotations(NodeList<AnnotationExpr> annotations) {
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        setAsParentNodeOf(annotations);
        this.annotations = assertNotNull(annotations);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations());
    }

    public void removeDimension() {
        setDimension(null);
    }
}

