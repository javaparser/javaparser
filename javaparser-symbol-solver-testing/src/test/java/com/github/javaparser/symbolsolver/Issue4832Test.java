/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue4832Test extends AbstractResolutionTest {

    @Test()
    void test() {
        String code = "public class Stream_NoImports {\n"
                + "    public java.util.stream.Stream<java.lang.String> simpleToList() {\n"
                + "       return java.util.stream.Stream.of(\"a\", \"b\", \"c\");\n"
                + "    }\n"
                + "}";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(code);

        // Find all the calculations with two sides:
        cu.findAll(MethodCallExpr.class).forEach(mc -> {
            // Find out what type it has:
            ResolvedType resolvedType = mc.calculateResolvedType();
            assertEquals("java.util.stream.Stream<java.lang.String>", resolvedType.describe());
        });
    }
}
