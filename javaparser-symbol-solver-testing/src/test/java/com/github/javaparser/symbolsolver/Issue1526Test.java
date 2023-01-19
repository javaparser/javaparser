/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assumptions.assumeTrue;


/**
 * CompilationUnitContext.solveType(String name, TypeSolver typeSolver) checks package and imports in wrong order.
 * @see <a href="https://github.com/javaparser/javaparser/issues/1526">https://github.com/javaparser/javaparser/issues/1526</a>
 */
public class Issue1526Test extends AbstractSymbolResolutionTest {

    private final Path testRoot = adaptPath("src/test/resources/issue1526");
    private final Path rootCompiles = testRoot.resolve("compiles");
    private final Path rootErrors = testRoot.resolve("errors");

    @Test
    public void givenImport_whenCompiles_expectPass() throws IOException {
        Path root = rootCompiles;
        Path file = rootCompiles.resolve("a/b/c/ExampleClass.java");

        assertDoesNotThrow(() -> {
            doTest(root, file);
        });
    }

    @Test
    public void givenImportCommentOut_whenCompiles_expectFail() throws IOException {
        Path root = rootErrors;
        Path file = rootErrors.resolve("a/b/c/ExampleClass.java");

        assertThrows(UnsolvedSymbolException.class, () -> {
            doTest(root, file);
        });
    }

    private void doTest(Path root, Path file) throws IOException {
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(root, new LeanParserConfiguration()));

        JavaParser javaParser = new JavaParser();
        javaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        ParseResult<CompilationUnit> cu = javaParser.parse(file);
        assumeTrue(cu.isSuccessful(), "the file should compile -- errors are expected when attempting to resolve.");

        cu.getResult().get().findAll(MethodCallExpr.class)
            .forEach(methodCallExpr -> {
                methodCallExpr.resolve();
                methodCallExpr.calculateResolvedType();
            });
    }

}
