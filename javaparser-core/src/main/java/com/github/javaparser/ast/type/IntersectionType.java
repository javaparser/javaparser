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
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.IntersectionTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * Represents a set of types. A given value of this type has to be assignable to at all of the element types.
 * As of Java 8 it is used in casts or while expressing bounds for generic types.
 * <p>
 * For example:
 * <code>public class A&lt;T extends Serializable &amp; Cloneable&gt; { }</code>
 * <p>
 * Or:
 * <code>void foo((Serializable &amp; Cloneable)myObject);</code>
 *
 * @since 3.0.0
 */
public class IntersectionType extends Type implements NodeWithAnnotations<IntersectionType> {

    private NodeList<ReferenceType<?>> elements;

    @AllFieldsConstructor
    public IntersectionType(NodeList<ReferenceType<?>> elements) {
        this(null, elements);
    }

    public IntersectionType(Range range, NodeList<ReferenceType<?>> elements) {
        super(range, new NodeList<>());
        setElements(elements);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public NodeList<ReferenceType<?>> getElements() {
        return elements;
    }

    public IntersectionType setElements(final NodeList<ReferenceType<?>> elements) {
        assertNotNull(elements);
        notifyPropertyChange(ObservableProperty.ELEMENTS, this.elements, elements);
        if (this.elements != null)
            this.elements.setParentNode(null);
        this.elements = elements;
        setAsParentNodeOf(elements);
        return this;
    }

    @Override
    public IntersectionType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (IntersectionType) super.setAnnotations(annotations);
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getElements(), getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public IntersectionType clone() {
        return (IntersectionType) accept(new CloneVisitor(), null);
    }

    @Override
    public IntersectionTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.intersectionTypeMetaModel;
    }
}
