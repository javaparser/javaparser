/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.LongLiteralExprMetaModel;
import java.math.BigInteger;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.hasUnaryMinusAsParent;
import com.github.javaparser.ast.Node;

/**
 * All ways to specify a long literal.
 *
 * <ul>
 * <li>{@code 8934l}</li>
 * <li>{@code 0x01L}</li>
 * <li>{@code 022l}</li>
 * <li>{@code 0B10101010L}</li>
 * <li>{@code 99999999L}</li>
 * </ul>
 *
 * @author Julio Vilmar Gesser
 */
public class LongLiteralExpr extends LiteralStringValueExpr {

    public static final String MAX_63_BIT_UNSIGNED_VALUE_AS_STRING = "9223372036854775808L";

    public static final BigInteger MAX_63_BIT_UNSIGNED_VALUE_AS_BIG_INTEGER = new BigInteger("9223372036854775808");

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

    /**
     * @deprecated This function is deprecated in favor of {@link #LongLiteralExpr(String)}. Please refer to the {@link
     * #asNumber()} function for valid formats and how to construct literals holding negative values.
     */
    @Deprecated
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

    /**
     * @return the literal value as an long while respecting different number representations
     * @deprecated This function has issues with corner cases, such as 9223372036854775808L, so please use {@link
     * LongLiteralExpr#asNumber()}. It will be made private or merged with {@link LongLiteralExpr#asNumber()} in future
     * releases
     */
    @Deprecated
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
     * This function returns a representation of the literal value as a number. This will return a long, except for the
     * case when the literal has the value {@code 9223372036854775808L}. This special literal is only allowed in
     * the expression {@code -9223372036854775808L} which represents <code>Long.MIN_VALUE</code>). However
     * 9223372036854775808 (2^63) is out of range of long, which is -(2^63) to (2^63)-1 and thus a BigInteger must be
     * returned.
     *
     * <p>Note, that this function will NOT return a negative number if the literal was specified in decimal, since
     * according to the language specification (chapter 3.10.1) an expression such as {@code -1L} is represented by
     * a unary * expression with a minus operator and the literal {@code 1L}. It is however possible to represent
     * negative * numbers in a literal directly,  i.e. by using the binary or hexadecimal representation. For example
     * {@code 0xffff_ffff_ffff_ffffL} represents the value <code>-1L</code>.
     *
     * @return the literal value as a number while respecting different number representations
     */
    public Number asNumber() {
        if (Objects.equals(value, MAX_63_BIT_UNSIGNED_VALUE_AS_STRING) && hasUnaryMinusAsParent(this)) {
            return MAX_63_BIT_UNSIGNED_VALUE_AS_BIG_INTEGER;
        }
        return asLong();
    }

    /**
     * @deprecated This function is deprecated in favor of {@link #setValue(String)}. Please refer to the {@link
     * #asNumber()} function for valid formats and how to construct literals holding negative values.
     */
    @Deprecated
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLongLiteralExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LongLiteralExpr asLongLiteralExpr() {
        return this;
    }

    @Override
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
