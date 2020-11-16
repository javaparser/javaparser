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

import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel;
import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;
import static org.junit.jupiter.api.Assertions.*;

/**
 * See JEP305 for switch pattern matching for instanceof
 * https://bugs.openjdk.java.net/browse/JDK-8181287
 *
 * <pre>
 * The instanceof grammar is extended accordingly:
 *
 * RelationalExpression:
 *      ...
 *      RelationalExpression instanceof ReferenceType
 *      RelationalExpression instanceof Pattern
 *
 * Pattern:
 *      ReferenceType Identifier
 * </pre>
 */
class InstanceOfExprTest {

    @Test
    void annotationsOnTheType_patternExpression() {
        InstanceOfExpr expr = TestParser.parseExpression(LanguageLevel.JAVA_14, "obj instanceof @A @DA String s");

        assertThat(expr.getType().getAnnotations())
                .containsExactly(
                        new MarkerAnnotationExpr("A"),
                        new MarkerAnnotationExpr("DA")
                );
    }

    @Test
    void annotationsOnTheType_referenceTypeExpression() {
        InstanceOfExpr expr = TestParser.parseExpression(LanguageLevel.JAVA_14, "obj instanceof @A @DA String");

        assertThat(expr.getType().getAnnotations())
                .containsExactly(
                        new MarkerAnnotationExpr("A"),
                        new MarkerAnnotationExpr("DA")
                );
    }

    @Test
    void instanceOf_patternExpression() {
        String x = "obj instanceof String s";
        InstanceOfExpr expr = TestParser.parseExpression(LanguageLevel.JAVA_14, x);

        assertEquals("obj", expr.getExpression().toString());
        assertEquals("String", expr.getType().asString());
        assertTrue(expr.getPattern().isPresent());

        PatternExpr patternExpr = expr.getPattern().get();
        assertEquals("String", patternExpr.getType().asString());
        assertEquals("s", patternExpr.getName().asString());

        //
        assertTrue(expr.getName().isPresent());
        assertEquals("s", expr.getName().get().asString());
    }

    @Test
    void instanceOf_referenceTypeExpression() {
        String x = "obj instanceof String";
        InstanceOfExpr expr = TestParser.parseExpression(LanguageLevel.JAVA_14, x);

        assertEquals("obj", expr.getExpression().toString());
        assertEquals(String.class.getSimpleName(), expr.getType().asString());
        assertFalse(expr.getPattern().isPresent());

        //
        assertFalse(expr.getName().isPresent());
    }



    /*
     * resolution / scoping tests?
     *
     * <pre>
     * {@code
     * if (!(obj instanceof String s)) {
     *     .. s.contains(..) ..
     * } else {
     *     .. s.contains(..) ..
     * }
     * }
     * </pre>
     *
     * Allowed / in scope: {@code if (obj instanceof String s && s.length() > 5) {..}}
     * Not in scope:       {@code if (obj instanceof String s || s.length() > 5) {..}}
     *
     */


}
