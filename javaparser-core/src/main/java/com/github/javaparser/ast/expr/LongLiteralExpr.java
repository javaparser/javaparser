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

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.LongLiteralExprMetaModel;
import com.github.javaparser.TokenRange;

import java.math.BigInteger;
import java.util.Objects;
import java.util.function.Consumer;
import java.util.Optional;

import com.github.javaparser.ast.Generated;

import static com.github.javaparser.utils.Utils.hasUnaryMinusAsParent;

/**
 * All ways to specify a long literal.
 * <ul>
 * <li><code>8934l</code></li>
 * <li><code>0x01L</code></li>
 * <li><code>022l</code></li>
 * <li><code>0B10101010L</code></li>
 * <li><code>99999999L</code></li>
 * </ul>
 *
 * @author Julio Vilmar Gesser
 */
public class LongLiteralExpr extends LiteralStringValueExpr {

    public LongLiteralExpr() {
        this(null, "0");
    }

    @AllFieldsConstructor
    public LongLiteralExpr(final String value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LongLiteralExpr(TokenRange tokenRange, String value) {
        super(tokenRange, value);
        customInitialization();
    }

    public LongLiteralExpr(final long value) {
        this(null, String.valueOf(value));
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
     * @return the literal value as an long while respecting different number representations
     * @deprecated Will be made private or merged with {@link LongLiteralExpr#asNumber()} in future releases
     */
    public long asLong() {
        String result = value.replaceAll("_", "");
        char lastChar = result.charAt(result.length() - 1);
        if (lastChar == 'l' || lastChar == 'L') {
            result = result.substring(0, result.length() - 1);
        }
        if (result.startsWith("0x") || result.startsWith("0X")) {
            return Long.parseUnsignedLong(result.substring(2), 16);
        }
        if (result.startsWith("0b") || result.startsWith("0B")) {
            return Long.parseUnsignedLong(result.substring(2), 2);
        }
        if (result.length() > 1 && result.startsWith("0")) {
            return Long.parseUnsignedLong(result.substring(1), 8);
        }
        return Long.parseLong(result);
    }

    /**
     * This function returns a representation of the literal values as a number. This will return a long, except for the
     * case when the literal has the value 9223372036854775808L (which is only allowed in the expression
     * <code>-9223372036854775808L</code>) and returns a BigInteger.
     * <p>
     * Note, that this function will NOT return a negative number if the literal was specified in decimal, since *
     * according to the language specification an expression such as <code>-1L</code> is represented by a unary *
     * expression with a minus operator and the literal <code>1L</code>. It is however possible to represent negative *
     * numbers in a literal directly, i.e. by using the binary or hexadecimal representation. For example *
     * <code>0xffff_ffff_ffff_ffffL</code> represents the value <code>-1L</code>.
     *
     * @return the literal value as a number while respecting different number representations
     */
    public Number asNumber() {
        /* we need to handle the special case for the literal 9223372036854775808L, which is used to
         * represent Integer.MIN_VALUE (-9223372036854775808L) as a combination of a UnaryExpr and a
         * LongLiteralExpr. However 9223372036854775808L cannot be represented in a long, so we need
         * to return a BigInteger
         */
        if (Objects.equals(value, "9223372036854775808L") && hasUnaryMinusAsParent(this)) {
            return new BigInteger("9223372036854775808");
        } else {
            return asLong();
        }
    }

    public LongLiteralExpr setLong(long value) {
        this.value = String.valueOf(value);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LongLiteralExpr clone() {
        return (LongLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LongLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.longLiteralExprMetaModel;
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
    public boolean isLongLiteralExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LongLiteralExpr asLongLiteralExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLongLiteralExpr(Consumer<LongLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LongLiteralExpr> toLongLiteralExpr() {
        return Optional.of(this);
    }
}
