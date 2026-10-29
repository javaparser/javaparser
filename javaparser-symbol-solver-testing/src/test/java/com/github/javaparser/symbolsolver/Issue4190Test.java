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
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
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

        Path filePath = issueResourcesPath.resolve("com/example/service/impl/RecordServiceImpl.java");

        CompilationUnit cu = parser.parse(filePath).getResult().get();

        assertDoesNotThrow(() -> cu.findAll(MethodDeclaration.class).forEach(method -> method.resolve()));
    }

    @Test
    void historicalIssue4190PathDoesNotCauseStackOverflow() throws IOException {
        Path issueResourcesPath = adaptPath("src/test/resources/issue4190");

        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(issueResourcesPath);

        ParserConfiguration previousConfiguration = StaticJavaParser.getParserConfiguration();

        try {
            StaticJavaParser.setConfiguration(new ParserConfiguration()
                    .setSymbolResolver(new JavaSymbolSolver(
                            new CombinedTypeSolver(new ReflectionTypeSolver(), javaParserTypeSolver))));

            Path filePath = issueResourcesPath.resolve("com/example/service/impl/RecordServiceImpl.java");

            assertDoesNotThrow(() -> StaticJavaParser.parse(filePath)
                    .accept(
                            new VoidVisitorAdapter<Void>() {
                                @Override
                                public void visit(MethodDeclaration methodDeclaration, Void arg) {
                                    try {
                                        methodDeclaration.resolve().getQualifiedName();
                                    } catch (Exception ignored) {
                                    }
                                }
                            },
                            null));
        } finally {
            StaticJavaParser.setConfiguration(previousConfiguration);
        }
    }

    @Test
    void missingSuperclassDoesNotBecomeItsOwnAncestor() throws IOException {
        ResolvedClassDeclaration declaration = missingSuperclassDeclaration();

        assertTrue(declaration.getAncestors(true).isEmpty());
    }

    @Test
    void strictAncestorLookupReportsMissingSuperclass() throws IOException {
        ResolvedClassDeclaration declaration = missingSuperclassDeclaration();

        assertThrows(UnsolvedSymbolException.class, () -> declaration.getAncestors(false));
    }

    @Test
    void directSuperclassLookupReportsMissingSuperclass() throws IOException {
        ResolvedClassDeclaration declaration = missingSuperclassDeclaration();

        assertThrows(UnsolvedSymbolException.class, declaration::getSuperClass);
    }

    @Test
    void sameSimpleNameFromAnotherPackageIsAllowed() {
        ResolvedClassDeclaration declaration = resolveClass(
                "package com.example.service;\n" + "class ArrayList extends java.util.ArrayList<String> {}\n");

        assertEquals("java.util.ArrayList", declaration.getSuperClass().get().getQualifiedName());
    }

    @Test
    void nestedSuperclassStillResolves() {
        ResolvedClassDeclaration declaration = resolveClass("package com.example.service;\n"
                + "class NestedChild extends java.util.AbstractMap.SimpleEntry<String, String> {\n"
                + "    NestedChild() { super(\"key\", \"value\"); }\n"
                + "}\n");

        assertEquals(
                "java.util.AbstractMap.SimpleEntry",
                declaration.getSuperClass().get().getQualifiedName());
    }

    private ResolvedClassDeclaration missingSuperclassDeclaration() throws IOException {
        Path issueResourcesPath = adaptPath("src/test/resources/issue4190");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(issueResourcesPath));

        JavaParser parser =
                new JavaParser(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));

        Path filePath = issueResourcesPath.resolve("com/example/service/impl/RecordServiceImpl.java");

        CompilationUnit cu = parser.parse(filePath).getResult().get();

        return cu.findFirst(ClassOrInterfaceDeclaration.class).get().resolve().asClass();
    }

    private ResolvedClassDeclaration resolveClass(String source) {
        JavaParser parser = new JavaParser(
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver())));

        CompilationUnit cu = parser.parse(source).getResult().get();

        return cu.findFirst(ClassOrInterfaceDeclaration.class).get().resolve().asClass();
    }
}
