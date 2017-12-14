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
import com.github.javaparser.metamodel.ArrayInitializerExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * The initialization of an array. In the following sample, the outer { } is an ArrayInitializerExpr.
 * It has two expressions inside: two ArrayInitializerExprs.
 * These have two expressions each, one has 1 and 1, the other two and two.
 * <br/><code>new int[][]{{1, 1}, {2, 2}};</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class ArrayInitializerExpr extends Expression {

    private NodeList<Expression> values;

    public ArrayInitializerExpr() {
        this(null, new NodeList<>());
    }

    @AllFieldsConstructor
    public ArrayInitializerExpr(NodeList<Expression> values) {
        this(null, values);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ArrayInitializerExpr(TokenRange tokenRange, NodeList<Expression> values) {
        super(tokenRange);
        setValues(values);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getValues() {
        return values;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ArrayInitializerExpr setValues(final NodeList<Expression> values) {
        assertNotNull(values);
        if (values == this.values) {
            return (ArrayInitializerExpr) this;
        }
        notifyPropertyChange(ObservableProperty.VALUES, this.values, values);
        if (this.values != null)
            this.values.setParentNode(null);
        this.values = values;
        setAsParentNodeOf(values);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < values.size(); i++) {
            if (values.get(i) == node) {
                values.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ArrayInitializerExpr clone() {
        return (ArrayInitializerExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ArrayInitializerExprMetaModel getMetaModel() {
        return JavaParserMetaModel.arrayInitializerExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < values.size(); i++) {
            if (values.get(i) == node) {
                values.set(i, (Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayInitializerExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayInitializerExpr asArrayInitializerExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayInitializerExpr(Consumer<ArrayInitializerExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayInitializerExpr> toArrayInitializerExpr() {
        return Optional.of(this);
    }
}
