/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
package org.javaparser.ast.expr;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.NormalAnnotationExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

/**
 * An annotation that has zero or more key-value pairs.<br/><code>@Mapping(a=5, d=10)</code>
 * @author Julio Vilmar Gesser
 */
public class NormalAnnotationExpr extends AnnotationExpr {

    private NodeList<MemberValuePair> pairs;

    public NormalAnnotationExpr() {
        this(null, new Name(), new NodeList<>());
    }

    @AllFieldsConstructor
    public NormalAnnotationExpr(final Name name, final NodeList<MemberValuePair> pairs) {
        this(null, name, pairs);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public NormalAnnotationExpr(TokenRange tokenRange, Name name, NodeList<MemberValuePair> pairs) {
        super(tokenRange, name);
        setPairs(pairs);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<MemberValuePair> getPairs() {
        return pairs;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NormalAnnotationExpr setPairs(final NodeList<MemberValuePair> pairs) {
        assertNotNull(pairs);
        if (pairs == this.pairs) {
            return (NormalAnnotationExpr) this;
        }
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
    public NormalAnnotationExpr addPair(String key, Expression value) {
        MemberValuePair memberValuePair = new MemberValuePair(key, value);
        getPairs().add(memberValuePair);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
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
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public NormalAnnotationExpr clone() {
        return (NormalAnnotationExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public NormalAnnotationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.normalAnnotationExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < pairs.size(); i++) {
            if (pairs.get(i) == node) {
                pairs.set(i, (MemberValuePair) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isNormalAnnotationExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public NormalAnnotationExpr asNormalAnnotationExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifNormalAnnotationExpr(Consumer<NormalAnnotationExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<NormalAnnotationExpr> toNormalAnnotationExpr() {
        return Optional.of(this);
    }
}
