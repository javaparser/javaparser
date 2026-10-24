/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

class CastMethodReferenceTest {
    @ParameterizedTest
    @ValueSource(
            strings = {
                "this::run",
                "Outer.this::run",
                "receiver::run",
                "receiver.field::run",
                "getReceiver()::run",
                "receivers[0]::run",
                "(receiver)::run",
                "(flag ? first : second)::run",
                "this::<String>run",
                "getReceiver()::<String>run",
                "super::run",
                "Outer.super::run",
                "Type::run",
                "Type::<String>run",
                "Type::new",
                "Type<String>::new",
                "int[]::new"
            })
    void methodReferenceIsTheCastOperand(String reference) {
        String source = "(Runnable) " + reference;
        Expression expression = StaticJavaParser.parseExpression(source);
        assertTrue(expression.isCastExpr(), expression::toString);
        CastExpr cast = expression.asCastExpr();
        assertEquals("Runnable", cast.getType().asString());
        MethodReferenceExpr operand = cast.getExpression().asMethodReferenceExpr();
        assertEquals(reference, operand.getTokenRange().get().toString());
        assertEquals(source, cast.getTokenRange().get().toString());
        assertEquals(source.indexOf("::"), operand.getScope().getRange().get().end.column);
        assertSame(cast, operand.getParentNode().get());
        assertEquals(cast, StaticJavaParser.parseExpression(cast.toString()));
    }

    @Test
    void nestedCastsKeepTheirOrder() {
        CastExpr outer = StaticJavaParser.parseExpression("(Object) (Runnable) this::run")
                .asCastExpr();
        CastExpr inner = outer.getExpression().asCastExpr();
        assertEquals("Object", outer.getType().asString());
        assertEquals("Runnable", inner.getType().asString());
        assertTrue(inner.getExpression().isMethodReferenceExpr());
    }

    @Test
    void intersectionCastWrapsMethodReference() {
        CastExpr cast = StaticJavaParser.parseExpression("(Runnable & Serializable) this::run")
                .asCastExpr();
        assertTrue(cast.getType().isIntersectionType());
        assertEquals(2, cast.getType().asIntersectionType().getElements().size());
        assertTrue(cast.getExpression().isMethodReferenceExpr());
    }

    @Test
    void typeArgumentsAreAttachedToTheMethodReference() {
        MethodReferenceExpr reference = StaticJavaParser.parseExpression("(Runnable) this::<String>run")
                .asCastExpr()
                .getExpression()
                .asMethodReferenceExpr();
        assertEquals("String", reference.getTypeArguments().get().get(0).asString());
        assertEquals("run", reference.getIdentifier());
        assertTrue(reference.getScope().isThisExpr());
    }

    @Test
    void castInsideParenthesesRemainsTheReferenceScope() {
        MethodReferenceExpr reference =
                StaticJavaParser.parseExpression("((Runnable) receiver)::run").asMethodReferenceExpr();
        assertTrue(reference.getScope().asEnclosedExpr().getInner().isCastExpr());
    }

    @Test
    void castInsideConditionalArmStaysInsideThatArm() {
        ConditionalExpr conditional = StaticJavaParser.parseExpression("flag ? (Runnable) this::run : other")
                .asConditionalExpr();
        assertTrue(conditional.getThenExpr().asCastExpr().getExpression().isMethodReferenceExpr());
    }

    @Test
    void castInsideEqualityRemainsTheLeftOperand() {
        BinaryExpr binary = StaticJavaParser.parseExpression("(Runnable) this::run == other")
                .asBinaryExpr();
        assertTrue(binary.getLeft().asCastExpr().getExpression().isMethodReferenceExpr());
        assertEquals(BinaryExpr.Operator.EQUALS, binary.getOperator());
    }

    @ParameterizedTest
    @ValueSource(strings = {"(int) +value", "(int) -value", "(Runnable) value", "(Runnable) () -> run()"})
    void ordinaryCastsKeepTheirOperands(String source) {
        Expression expression = StaticJavaParser.parseExpression(source);
        assertTrue(expression.isCastExpr());
        assertFalse(expression.asCastExpr().getExpression().isMethodReferenceExpr());
    }

    @Test
    void positionsAlsoWorkWithoutStoredTokens() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setStoreTokens(false));
        CastExpr cast =
                parser.parseExpression("(Runnable) this::run").getResult().get().asCastExpr();
        assertFalse(cast.getTokenRange().isPresent());
        assertTrue(cast.getExpression().isMethodReferenceExpr());
    }

    @ParameterizedTest
    @ValueSource(strings = {"(Runnable) this::", "(Runnable) this::run++"})
    void incompleteOrPostfixedReferencesAreRejected(String source) {
        assertFalse(new JavaParser().parseExpression(source).isSuccessful());
    }
}
