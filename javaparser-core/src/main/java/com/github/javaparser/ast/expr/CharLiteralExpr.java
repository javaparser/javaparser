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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.CharLiteralExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.StringEscapeUtils;
import com.github.javaparser.utils.Utils;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * A literal character.
 * <br/><code>'a'</code>
 * <br/><code>'\t'</code>
 * <br/><code>'Ω'</code>
 * <br/><code>'\177'</code>
 * <br/><code>'💩'</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class CharLiteralExpr extends LiteralStringValueExpr {

    public CharLiteralExpr() {
        this(null, "?");
    }

    @AllFieldsConstructor
    public CharLiteralExpr(String value) {
        this(null, value);
    }

    /**
     * Constructs a CharLiteralExpr with given escaped character.
     *
     * @param value a char
     */
    public CharLiteralExpr(char value) {
        this(null, StringEscapeUtils.escapeJava(String.valueOf(value)));
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public CharLiteralExpr(TokenRange tokenRange, String value) {
        super(tokenRange, value);
        customInitialization();
    }

    /**
     * Utility method that creates a new StringLiteralExpr. Escapes EOL characters.
     */
    public static CharLiteralExpr escape(String string) {
        return new CharLiteralExpr(Utils.escapeEndOfLines(string));
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

    /**
     * @return the unescaped value character of this literal
     */
    public char asChar() {
        return StringEscapeUtils.unescapeJava(value).charAt(0);
    }

    /**
     * Sets the given char as the literal value
     *
     * @param value a char
     * @return this expression
     */
    public CharLiteralExpr setChar(char value) {
        this.value = String.valueOf(value);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public CharLiteralExpr clone() {
        return (CharLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public CharLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.charLiteralExprMetaModel;
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
    public boolean isCharLiteralExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public CharLiteralExpr asCharLiteralExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCharLiteralExpr(Consumer<CharLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CharLiteralExpr> toCharLiteralExpr() {
        return Optional.of(this);
    }
}
