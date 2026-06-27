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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

public class Issue2738Test extends AbstractSymbolResolutionTest {
    @Test
    void test() throws IOException {
        ParserConfiguration config = new ParserConfiguration();
        Path pathToSourceFile = adaptPath("src/test/resources/issue2738");
        TypeSolver cts = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(pathToSourceFile));
        config.setSymbolResolver(new JavaSymbolSolver(cts));

        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(pathToSourceFile.resolve("B.java"));

        // We shouldn't throw an exception
        assertDoesNotThrow(() -> cu.findAll(MethodCallExpr.class).stream().map(MethodCallExpr::resolve));
    }
}
