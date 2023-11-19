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
import com.github.javaparser.metamodel.IntegerLiteralExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.hasUnaryMinusAsParent;
import com.github.javaparser.ast.Node;

/**
 * All ways to specify an int literal.
 *
 * <ul>
 * <li>{@code 8934}</li>
 * <li>{@code 0x01}</li>
 * <li>{@code 022}</li>
 * <li>{@code 0B10101010}</li>
 * </ul>
 *
 * @author Julio Vilmar Gesser
 */
public class IntegerLiteralExpr extends LiteralStringValueExpr {

    public static final String MAX_31_BIT_UNSIGNED_VALUE_AS_STRING = "2147483648";

    public static final long MAX_31_BIT_UNSIGNED_VALUE_AS_LONG = 2147483648L;

    public IntegerLiteralExpr() {
        this(null, "0");
    }

    @AllFieldsConstructor
    public IntegerLiteralExpr(final String value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public IntegerLiteralExpr(TokenRange tokenRange, String value) {
        super(tokenRange, value);
        customInitialization();
    }

    /**
     * @deprecated This function is deprecated in favor of {@link #IntegerLiteralExpr(String)}. Please refer to the
     * {@link #asNumber()} function for valid formats and how to construct literals holding negative values.
     */
    @Deprecated
    public IntegerLiteralExpr(final int value) {
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
     * @return the literal value as an integer while respecting different number representations
     * @deprecated This function has issues with corner cases, such as 2147483648, so please use {@link
     * IntegerLiteralExpr#asNumber()}. It will be made private or merged with {@link IntegerLiteralExpr#asNumber()} in
     * future releases
     */
    @Deprecated
    public int asInt() {
        String result = value.replaceAll("_", "");
        if (result.startsWith("0x") || result.startsWith("0X")) {
            return Integer.parseUnsignedInt(result.substring(2), 16);
        }
        if (result.startsWith("0b") || result.startsWith("0B")) {
            return Integer.parseUnsignedInt(result.substring(2), 2);
        }
        if (result.length() > 1 && result.startsWith("0")) {
            return Integer.parseUnsignedInt(result.substring(1), 8);
        }
        return Integer.parseInt(result);
    }

    /**
     * This function returns a representation of the literal value as a number. This will return an integer, except for
     * the case when the literal has the value {@code 2147483648}. This special literal is only allowed in the
     * expression {@code -2147483648} which represents <code>Integer.MIN_VALUE</code>). However 2147483648 (2^31)
     * is out of range of int, which is -(2^31) to (2^31)-1 and thus a long must be returned.
     *
     * <p>Note, that this function will NOT return a negative number if the literal was specified in decimal, since
     * according to the language specification (chapter 3.10.1) an expression such as {@code -1} is represented by
     * a unary expression with a minus operator and the literal {@code 1}. It is however possible to represent
     * negative numbers in a literal directly, i.e. by using the binary or hexadecimal representation. For example
     * {@code 0xffff_ffff} represents the value <code> -1</code>.
     *
     * @return the literal value as a number while respecting different number representations
     */
    public Number asNumber() {
        if (Objects.equals(value, MAX_31_BIT_UNSIGNED_VALUE_AS_STRING) && hasUnaryMinusAsParent(this)) {
            return MAX_31_BIT_UNSIGNED_VALUE_AS_LONG;
        }
        return asInt();
    }

    /**
     * @deprecated This function is deprecated in favor of {@link #setValue(String)}. Please refer to the {@link
     * #asNumber()} function for valid formats and how to construct literals holding negative values.
     */
    @Deprecated
    public IntegerLiteralExpr setInt(int value) {
        this.value = String.valueOf(value);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public IntegerLiteralExpr clone() {
        return (IntegerLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public IntegerLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.integerLiteralExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isIntegerLiteralExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public IntegerLiteralExpr asIntegerLiteralExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifIntegerLiteralExpr(Consumer<IntegerLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<IntegerLiteralExpr> toIntegerLiteralExpr() {
        return Optional.of(this);
    }
}
