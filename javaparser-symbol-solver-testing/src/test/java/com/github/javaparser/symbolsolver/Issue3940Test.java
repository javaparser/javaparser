/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

public class Issue3940Test extends AbstractResolutionTest {

    @Test
    void selfReferentialGenericTypeShouldNotCauseStackOverflow() {
        JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));

        CompilationUnit cu = parser.parse(
                "package org.apache.logging.log4j.core.async;\n"
                        + "\n"
                        + "public class AsyncLoggerConfig {\n"
                        + "    public static class RootLogger {\n"
                        + "        public static class Builder<B extends Builder<B>> extends RootLogger.Builder<B> {\n"
                        + "            @Override\n"
                        + "            public AsyncLoggerConfig build() {\n"
                        + "                return new AsyncLoggerConfig();\n"
                        + "            }\n"
                        + "        }\n"
                        + "    }\n"
                        + "}");

        for (MethodCallExpr methodCallExpr : cu.findAll(MethodCallExpr.class)) {
            assertDoesNotThrow(() -> methodCallExpr.resolve());
        }
    }
}
