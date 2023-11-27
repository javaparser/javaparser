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

package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.ProjectRoot;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

import static com.github.javaparser.utils.CodeGenerationUtils.classLoaderRoot;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SymbolSolverCollectionStrategyTest {

    private final Path root = classLoaderRoot(SymbolSolverCollectionStrategyTest.class).resolve("../../../javaparser-core").normalize();
    private final ProjectRoot projectRoot = new SymbolSolverCollectionStrategy().collect(root);

    @Test
    void resolveExpressions() throws IOException {
        SourceRoot sourceRoot = projectRoot.getSourceRoot(root.resolve("src/main/java")).get();
        AtomicInteger unresolved = new AtomicInteger();
        for (ParseResult<CompilationUnit> parseResult : sourceRoot.tryToParse()) {
            parseResult.ifSuccessful(compilationUnit -> {
                for (MethodDeclaration expr : compilationUnit.findAll(MethodDeclaration.class)) {
                    try {
                        expr.resolve().getQualifiedSignature();
                    } catch (UnsupportedOperationException e) {
                        // not supported operation, just skip
                    } catch (Exception e) {
                        unresolved.getAndIncrement();
                        Log.error(e, "Unable to resolve %s from %s", () -> expr, () -> compilationUnit.getStorage().get().getPath());
                    }
                }
            });
        }
        // not too many MethodDeclarations should be unresolved
        assertTrue(unresolved.get() < 10);
    }
    
    @Test
    void resolveMultiSourceRoots() {
        String[] relativeRootDir = {"/src/main/java-templates", "src/main/java", "src/main/javacc-support", "target/generated-sources/javacc", "target/generated-sources/java-templates", "src/main/java-templates"};
        Path mainDirectory = classLoaderRoot(SymbolSolverCollectionStrategyTest.class).resolve("../../../javaparser-core").normalize();
        ProjectRoot projectRoot = new SymbolSolverCollectionStrategy().collect(mainDirectory);
        List<com.github.javaparser.utils.SourceRoot> sourceRoots = projectRoot.getSourceRoots();
        // get all source root directories
        List<String> roots = projectRoot.getSourceRoots().stream().map(s -> s.getRoot().toString()).collect(Collectors.toList());
        // verify each member of the list
        Arrays.stream(relativeRootDir).forEach(rrd -> {
            Path p = Paths.get(mainDirectory.toString(), rrd);
            assertTrue(roots.contains(p.toString()));
        });
    }
}
