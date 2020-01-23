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
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import org.javaparser.metamodel.CharLiteralExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.utils.StringEscapeUtils;
import org.javaparser.utils.Utils;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

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
public class CharLiteralExpr extends LiteralStringValueExpr {

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
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
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
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
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
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public CharLiteralExpr clone() {
        return (CharLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public CharLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.charLiteralExprMetaModel;
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
    public boolean isCharLiteralExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public CharLiteralExpr asCharLiteralExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCharLiteralExpr(Consumer<CharLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CharLiteralExpr> toCharLiteralExpr() {
        return Optional.of(this);
    }
}
