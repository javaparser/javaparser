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
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.BooleanLiteralExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import com.github.javaparser.ast.Generated;

/**
 * The boolean literals.
 * <br/><code>true</code>
 * <br/><code>false</code>
 *
 * @author Julio Vilmar Gesser
 */
public class BooleanLiteralExpr extends LiteralExpr {

    private boolean value;

    public BooleanLiteralExpr() {
        this(null, false);
    }

    @AllFieldsConstructor
    public BooleanLiteralExpr(boolean value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public BooleanLiteralExpr(TokenRange tokenRange, boolean value) {
        super(tokenRange);
        setValue(value);
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
    public boolean getValue() {
        return value;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BooleanLiteralExpr setValue(final boolean value) {
        if (value == this.value) {
            return (BooleanLiteralExpr) this;
        }
        notifyPropertyChange(ObservableProperty.VALUE, this.value, value);
        this.value = value;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public BooleanLiteralExpr clone() {
        return (BooleanLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public BooleanLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.booleanLiteralExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBooleanLiteralExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BooleanLiteralExpr asBooleanLiteralExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBooleanLiteralExpr(Consumer<BooleanLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BooleanLiteralExpr> toBooleanLiteralExpr() {
        return Optional.of(this);
    }
}
