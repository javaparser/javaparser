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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

public class Issue4450Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() throws IOException {
        ParserConfiguration config = new ParserConfiguration();
        Path issueResourcesPath = adaptPath("src/test/resources/issue4450");
        JavaParserTypeSolver jpts = new JavaParserTypeSolver(issueResourcesPath);
        CombinedTypeSolver cts = new CombinedTypeSolver();
        cts.add(new ReflectionTypeSolver(false));
        cts.add(jpts);
        config.setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(config);
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(issueResourcesPath.resolve("a/RefCycleClass.java"));

        // We shouldn't throw a mismatched symbol
        assertDoesNotThrow(() -> cu.findAll(NameExpr.class).stream()
                .map(NameExpr::resolve)
                .findAny()
                .get());

        cu.findAll(NameExpr.class).forEach(expr -> {
            expr.resolve().getName();
        });
    }
}
