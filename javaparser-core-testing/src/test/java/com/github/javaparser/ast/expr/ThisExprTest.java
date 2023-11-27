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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ThisExprTest {
    @Test
    void justThis() {
        Expression expr = parseExpression("this");

        assertTrue(expr.isThisExpr());
    }

    @Test
    void justThisName() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setStoreTokens(false));
        ParseResult<Expression> parseResult = javaParser.parseExpression("this.c");
        FieldAccessExpr fieldAccess = parseResult.getResult().get().asFieldAccessExpr();
        assertEquals("c", fieldAccess.getName().asString());
    }

    @Test
    void singleScopeThis() {
        Expression expr = parseExpression("A.this");

        Name className = expr.asThisExpr().getTypeName().get();

        assertEquals("A", className.asString());
    }

    @Test
    void singleScopeThisName() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setStoreTokens(false));
        ParseResult<Expression> parseResult = javaParser.parseExpression("A.this.c");
        FieldAccessExpr fieldAccess = parseResult.getResult().get().asFieldAccessExpr();
        assertEquals("c", fieldAccess.getName().asString());
    }

    @Test
    void multiScopeThis() {
        Expression expr = parseExpression("a.B.this");

        Name className = expr.asThisExpr().getTypeName().get();

        assertEquals("a.B", className.asString());
    }

    @Test
    void multiScopeThisName() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setStoreTokens(false));
        ParseResult<Expression> parseResult = javaParser.parseExpression("a.B.this.c");
        FieldAccessExpr fieldAccess = parseResult.getResult().get().asFieldAccessExpr();
        assertEquals("c", fieldAccess.getName().asString());
    }

}
