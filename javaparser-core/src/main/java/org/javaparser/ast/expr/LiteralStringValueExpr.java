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
import org.javaparser.ast.Node;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.metamodel.LiteralStringValueExprMetaModel;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.TokenRange;
import org.javaparser.ast.Generated;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * Any literal value that is stored internally as a String.
 */
public abstract class LiteralStringValueExpr extends LiteralExpr {

    protected String value;

    @AllFieldsConstructor
    public LiteralStringValueExpr(final String value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public LiteralStringValueExpr(TokenRange tokenRange, String value) {
        super(tokenRange);
        setValue(value);
        customInitialization();
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public String getValue() {
        return value;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public LiteralStringValueExpr setValue(final String value) {
        assertNotNull(value);
        if (value == this.value) {
            return (LiteralStringValueExpr) this;
        }
        notifyPropertyChange(ObservableProperty.VALUE, this.value, value);
        this.value = value;
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public LiteralStringValueExpr clone() {
        return (LiteralStringValueExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public LiteralStringValueExprMetaModel getMetaModel() {
        return JavaParserMetaModel.literalStringValueExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLiteralStringValueExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public LiteralStringValueExpr asLiteralStringValueExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLiteralStringValueExpr(Consumer<LiteralStringValueExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LiteralStringValueExpr> toLiteralStringValueExpr() {
        return Optional.of(this);
    }
}
