/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class PolyExpressionResolutionTest extends AbstractResolutionTest {

    @BeforeEach
    void setup() {
    }

    @Test
    void methodReferenceExpressionAsPolyExpression() {
        Expression expr = StaticJavaParser.parseExpression("String::length");
        assertTrue(expr.isPolyExpression());
        assertFalse(expr.isStandaloneExpression());
    }

    @Test
    void lambdaExpressionAsPolyExpression() {
        Expression expr = StaticJavaParser.parseExpression("(s) -> s.toString()");
        assertTrue(expr.isPolyExpression());
        assertFalse(expr.isStandaloneExpression());
    }

    @Test
    void parenthesizedExpressionAsStandaloneExpression() {
        Expression expr = StaticJavaParser.parseExpression("(-1)");
        assertTrue(expr.isStandaloneExpression());
        assertFalse(expr.isPolyExpression());
    }

    @Test
    void objectCreationPolyExpressionTest() {
        Expression expr = StaticJavaParser.parseExpression("new ArrayList<>()");
        // see issue https://github.com/javaparser/javaparser/issues/2985
         assertFalse(expr.isPolyExpression());
         assertTrue(expr.isStandaloneExpression());
    }

    @Test
    void objectCreationStandaloneExpressionTest() {
        Expression expr = StaticJavaParser.parseExpression("new ArrayList()");
        assertFalse(expr.isPolyExpression());
        assertTrue(expr.isStandaloneExpression());

        expr = StaticJavaParser.parseExpression("new ArrayList<>().clear()");
        assertFalse(expr.isPolyExpression());
        assertTrue(expr.isStandaloneExpression());

        expr = StaticJavaParser.parseExpression("new ArrayList<String>()");
        assertFalse(expr.isPolyExpression());
        assertTrue(expr.isStandaloneExpression());
    }

    @Test
    void methodCallExpressionStandaloneExpressionInMethodCallContextTest() {
        Expression expr = StaticJavaParser.parseExpression("m(s.toString())").findAll(MethodCallExpr.class).get(1);
        assertFalse(expr.isPolyExpression());
        assertTrue(expr.isStandaloneExpression());
    }
    
    @Test
    void methodCallExpressionStandaloneExpressionInAssignementContextTest() {
        Expression expr = StaticJavaParser.parseExpression("x = s.toString()").findAll(MethodCallExpr.class).get(0);
        assertFalse(expr.isPolyExpression());
        assertTrue(expr.isStandaloneExpression());
    }
    
    @Test
    void methodCallExpressionPolyExpressionInAssignementContextTest() {
        Expression expr = StaticJavaParser.parseExpression("same = Util.<Integer, String>compare(p1, p2)").findAll(MethodCallExpr.class).get(0);
        assertFalse(expr.isPolyExpression());
        assertTrue(expr.isStandaloneExpression());
    }

    @Test
    void elidesTypeArgumentsTest() {
        Expression expr = StaticJavaParser.parseExpression("m()");
        assertTrue(expr.elidesTypeArguments());
        expr = StaticJavaParser.parseExpression("a.m()").findFirst(MethodCallExpr.class).get();
        assertTrue(expr.elidesTypeArguments());
        expr = StaticJavaParser.parseExpression("new A().m()").findFirst(MethodCallExpr.class).get();
        assertTrue(expr.elidesTypeArguments());
        expr = StaticJavaParser.parseExpression("new A<T>().<>m()").findFirst(MethodCallExpr.class).get();
        assertTrue(expr.elidesTypeArguments());
        expr = StaticJavaParser.parseExpression("new A<T>().<T>m()").findFirst(MethodCallExpr.class).get();
        assertFalse(expr.elidesTypeArguments());
    }

    @Test
    void appearsInAssignmentContextTest() {
        Expression expr = StaticJavaParser.parseExpression("a = m()").findFirst(MethodCallExpr.class).get();
        assertTrue(expr.appearsInAssignmentContext());
    }
    
    @Test
    void notAppearsInAssignmentContextTest() {
        Expression expr = StaticJavaParser.parseExpression("a.m()").findFirst(MethodCallExpr.class).get();
        assertFalse(expr.appearsInAssignmentContext());
    }
    
    @Test
    void notAppearsInInvocationContextTest() {
        Expression expr = StaticJavaParser.parseExpression("a = m()").findFirst(MethodCallExpr.class).get();
        assertFalse(expr.appearsInInvocationContext());
    }
    
    @Test
    void appearsInInvocationContextTest() {
        Expression expr = StaticJavaParser.parseExpression("a().m()").findAll(MethodCallExpr.class).get(1);
        assertTrue(expr.appearsInInvocationContext());
    }

}
