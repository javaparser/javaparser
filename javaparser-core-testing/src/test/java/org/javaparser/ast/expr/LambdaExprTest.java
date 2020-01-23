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

package org.javaparser.ast.expr;

import org.javaparser.TokenRange;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.body.Parameter;
import org.javaparser.ast.type.UnknownType;
import org.junit.jupiter.api.Test;

import static org.javaparser.StaticJavaParser.parseBlock;
import static org.javaparser.StaticJavaParser.parseExpression;
import static org.javaparser.utils.TestUtils.assertEqualsNoEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

class LambdaExprTest {
    @Test
    void lambdaRange1() {
        Expression expression = parseExpression("x -> y");
        assertRange("x", "y", expression);
    }

    @Test
    void lambdaRange2() {
        Expression expression = parseExpression("(x) -> y");
        assertRange("(", "y", expression);
    }

    private void assertRange(String startToken, String endToken, Node node) {
        TokenRange tokenRange = node.getTokenRange().get();
        assertEquals(startToken, tokenRange.getBegin().asString());
        assertEquals(endToken, tokenRange.getEnd().asString());
    }

    @Test
    void getExpressionBody() {
        LambdaExpr lambdaExpr = parseExpression("x -> y").asLambdaExpr();
        assertEquals("Optional[y]", lambdaExpr.getExpressionBody().toString());
    }

    @Test
    void getNoExpressionBody() {
        LambdaExpr lambdaExpr = parseExpression("x -> {y;}").asLambdaExpr();
        assertEquals("Optional.empty", lambdaExpr.getExpressionBody().toString());
    }

    @Test
    void oneParameterAndExpressionUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new Parameter(new UnknownType(), "a"), parseExpression("5"));
        assertEquals("a -> 5", expr.toString());
    }

    @Test
    void oneParameterAndStatementUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new Parameter(new UnknownType(), "a"), parseBlock("{return 5;}"));
        assertEqualsNoEol("a -> {\n    return 5;\n}", expr.toString());
    }

    @Test
    void multipleParametersAndExpressionUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new NodeList<>(new Parameter(new UnknownType(), "a"), new Parameter(new UnknownType(), "b")), parseExpression("5"));
        assertEquals("(a, b) -> 5", expr.toString());
    }

    @Test
    void multipleParametersAndStatementUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new NodeList<>(new Parameter(new UnknownType(), "a"), new Parameter(new UnknownType(), "b")), parseBlock("{return 5;}"));
        assertEqualsNoEol("(a, b) -> {\n    return 5;\n}", expr.toString());
    }

    @Test
    void zeroParametersAndStatementUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new NodeList<>(), parseBlock("{return 5;}"));
        assertEqualsNoEol("() -> {\n    return 5;\n}", expr.toString());
    }

}
