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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

public class Issue4190Test extends AbstractSymbolResolutionTest {

    @Test
    void missingAncestorSourceDoesNotCauseStackOverflow() throws IOException {
        Path issueResourcesPath = adaptPath("src/test/resources/issue4190");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(issueResourcesPath));

        JavaParser parser =
                new JavaParser(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));

        Path filePath =
                issueResourcesPath.resolve("com/example/service/impl/RecordServiceImpl.java");

        CompilationUnit cu = parser.parse(filePath).getResult().get();

        assertDoesNotThrow(() ->
                cu.findAll(MethodDeclaration.class).forEach(method -> method.resolve()));
    }

    @Test
    void historicalIssue4190PathDoesNotCauseStackOverflow() throws IOException {
        Path issueResourcesPath = adaptPath("src/test/resources/issue4190");

        JavaParserTypeSolver javaParserTypeSolver =
                new JavaParserTypeSolver(issueResourcesPath);

        StaticJavaParser.getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(
                        new CombinedTypeSolver(
                                new ReflectionTypeSolver(),
                                javaParserTypeSolver)));

        Path filePath =
                issueResourcesPath.resolve("com/example/service/impl/RecordServiceImpl.java");

        assertDoesNotThrow(() ->
                StaticJavaParser.parse(filePath).accept(new VoidVisitorAdapter<Void>() {
                    @Override
                    public void visit(MethodDeclaration methodDeclaration, Void arg) {
                        try {
                            methodDeclaration.resolve().getQualifiedName();
                        } catch (Exception ignored) {
                        }
                    }
                }, null));
    }
}
