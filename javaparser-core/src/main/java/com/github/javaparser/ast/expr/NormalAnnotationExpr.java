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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.NormalAnnotationExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * An annotation that has zero or more key-value pairs.<br/><code>@Mapping(a=5, d=10)</code>
 * @author Julio Vilmar Gesser
 */
public final class NormalAnnotationExpr extends AnnotationExpr {

    private NodeList<MemberValuePair> pairs;

    public NormalAnnotationExpr() {
        this(null, new Name(), new NodeList<>());
    }

    @AllFieldsConstructor
    public NormalAnnotationExpr(final Name name, final NodeList<MemberValuePair> pairs) {
        this(null, name, pairs);
    }

    public NormalAnnotationExpr(final Range range, final Name name, final NodeList<MemberValuePair> pairs) {
        super(range, name);
        setPairs(pairs);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public NodeList<MemberValuePair> getPairs() {
        return pairs;
    }

    public NormalAnnotationExpr setPairs(final NodeList<MemberValuePair> pairs) {
        assertNotNull(pairs);
        notifyPropertyChange(ObservableProperty.PAIRS, this.pairs, pairs);
        if (this.pairs != null)
            this.pairs.setParentNode(null);
        this.pairs = pairs;
        setAsParentNodeOf(pairs);
        return this;
    }

    /**
     * adds a pair to this annotation
     *
     * @return this, the {@link NormalAnnotationExpr}
     */
    public NormalAnnotationExpr addPair(String key, String value) {
        return addPair(key, new NameExpr(value));
    }

    /**
     * adds a pair to this annotation
     *
     * @return this, the {@link NormalAnnotationExpr}
     */
    public NormalAnnotationExpr addPair(String key, NameExpr value) {
        MemberValuePair memberValuePair = new MemberValuePair(key, value);
        getPairs().add(memberValuePair);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getPairs());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < pairs.size(); i++) {
            if (pairs.get(i) == node) {
                pairs.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public NormalAnnotationExpr clone() {
        return (NormalAnnotationExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public NormalAnnotationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.normalAnnotationExprMetaModel;
    }
}
