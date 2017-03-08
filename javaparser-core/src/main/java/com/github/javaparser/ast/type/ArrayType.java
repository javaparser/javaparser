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
import com.github.javaparser.utils.Pair;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.ast.NodeList.nodeList;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ArrayTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * To indicate that a type is an array, it gets wrapped in an ArrayType for every array level it has.
 * So, int[][] becomes ArrayType(ArrayType(int)).
 */
public class ArrayType extends ReferenceType implements NodeWithAnnotations<ArrayType> {

    private Type componentType;

    @AllFieldsConstructor
    public ArrayType(Type componentType, NodeList<AnnotationExpr> annotations) {
        this(null, componentType, annotations);
    }

    public ArrayType(Type type, AnnotationExpr... annotations) {
        this(type, nodeList(annotations));
    }

    public ArrayType(Range range, Type componentType, NodeList<AnnotationExpr> annotations) {
        super(range);
        setComponentType(componentType);
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

    public Type getComponentType() {
        return componentType;
    }

    public ArrayType setComponentType(final Type componentType) {
        assertNotNull(componentType);
        notifyPropertyChange(ObservableProperty.COMPONENT_TYPE, this.componentType, componentType);
        if (this.componentType != null)
            this.componentType.setParentNode(null);
        this.componentType = componentType;
        setAsParentNodeOf(componentType);
        return this;
    }

    /**
     * Takes lists of arrayBracketPairs, assumes the lists are ordered left to right and the pairs are ordered left to
     * right, mirroring the actual code. The type gets wrapped in ArrayTypes so that the outermost ArrayType corresponds
     * to the rightmost ArrayBracketPair.
     */
    @SafeVarargs
    public static Type wrapInArrayTypes(Type type, List<ArrayBracketPair>... arrayBracketPairLists) {
        for (int i = arrayBracketPairLists.length - 1; i >= 0; i--) {
            final List<ArrayBracketPair> arrayBracketPairList = arrayBracketPairLists[i];
            if (arrayBracketPairList != null) {
                for (int j = arrayBracketPairList.size() - 1; j >= 0; j--) {
                    ArrayBracketPair pair = arrayBracketPairList.get(j);
                    Range range = null;
                    if (type.getRange().isPresent() && pair.getRange().isPresent()) {
                        range = new Range(type.getBegin().get(), pair.getRange().get().end);
                    }
                    type = new ArrayType(range, type, pair.getAnnotations());
                }
            }
        }
        return type;
    }

    /**
     * Takes a type that may be an ArrayType. Unwraps ArrayTypes until the element type is found.
     *
     * @return a pair of the element type, and the unwrapped ArrayTypes, if any.
     */
    public static Pair<Type, List<ArrayBracketPair>> unwrapArrayTypes(Type type) {
        final List<ArrayBracketPair> arrayBracketPairs = new ArrayList<>(0);
        while (type instanceof ArrayType) {
            ArrayType arrayType = (ArrayType) type;
            arrayBracketPairs.add(new ArrayBracketPair(type.getRange().orElse(null), arrayType.getAnnotations()));
            type = arrayType.getComponentType();
        }
        return new Pair<>(type, arrayBracketPairs);
    }

    /**
     * Helper class that stores information about a pair of brackets.
     */
    public static class ArrayBracketPair {

        private Range range;

        private NodeList<AnnotationExpr> annotations = new NodeList<>();

        public ArrayBracketPair(Range range, NodeList<AnnotationExpr> annotations) {
            setRange(range);
            setAnnotations(annotations);
        }

        public NodeList<AnnotationExpr> getAnnotations() {
            return annotations;
        }

        public ArrayBracketPair setAnnotations(NodeList<AnnotationExpr> annotations) {
            this.annotations = assertNotNull(annotations);
            return this;
        }

        public ArrayBracketPair setRange(Range range) {
            this.range = range;
            return this;
        }

        public Optional<Range> getRange() {
            return Optional.ofNullable(range);
        }
    }

    @Override
    public ArrayType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (ArrayType) super.setAnnotations(annotations);
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public ArrayType clone() {
        return (ArrayType) accept(new CloneVisitor(), null);
    }

    @Override
    public ArrayTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.arrayTypeMetaModel;
    }
}
