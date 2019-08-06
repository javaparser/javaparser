/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.StringLiteralExprMetaModel;
import com.github.javaparser.utils.StringEscapeUtils;
import com.github.javaparser.utils.Utils;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.metamodel.TextBlockLiteralExprMetaModel;

/**
 * <h1>A text block</h1>
 * <h2>Java 13-</h2>
 * A text block is a multi-line string. It was introduced in JEP 355.
 * The content of "value" is byte-for-byte exactly what is in the source code.
 */
public class TextBlockLiteralExpr extends LiteralStringValueExpr {

    public TextBlockLiteralExpr() {
        this(null, "empty");
    }

    /**
     * Creates a text block literal expression from given string.
     *
     * @param value the value of the literal
     */
    @AllFieldsConstructor
    public TextBlockLiteralExpr(final String value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public TextBlockLiteralExpr(TokenRange tokenRange, String value) {
        super(tokenRange, value);
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public boolean isTextBlockLiteralExpr() {
        return true;
    }

    @Override
    public TextBlockLiteralExpr asTextBlockLiteralExpr() {
        return this;
    }

    @Override
    public Optional<TextBlockLiteralExpr> toTextBlockLiteralExpr() {
        return Optional.of(this);
    }

    public void ifTextBlockLiteralExpr(Consumer<TextBlockLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    public TextBlockLiteralExpr clone() {
        return (TextBlockLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public TextBlockLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.textBlockLiteralExprMetaModel;
    }
}
