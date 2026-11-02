/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
import static org.junit.jupiter.api.Assertions.assertFalse;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The compilation units parsed by a {@link JavaParserTypeSolver} must be resolvable, so that the nodes reached
 * through {@code toAst()} can be resolved without any extra configuration.
 */
class Issue5015Test {

    private static final String HELPER = "import java.util.HashMap;\n"
            + "public class Helper {\n"
            + "  private HashMap<String, String> map = new HashMap<>();\n"
            + "  public void register(String s) { map.containsKey(s); }\n"
            + "}\n";

    @TempDir
    Path srcDir;

    private void write(String fileName, String code) throws IOException {
        Files.write(srcDir.resolve(fileName), code.getBytes(StandardCharsets.UTF_8));
    }

    private static CompilationUnit parse(TypeSolver typeSolver, String code) {
        return new JavaParser(new ParserConfiguration()
                        .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                        .setSymbolResolver(new JavaSymbolSolver(typeSolver)))
                .parse(code)
                .getResult()
                .get();
    }

    /** Resolves the call to register, then navigates to its declaration with toAst(). */
    private static MethodDeclaration registerDeclaration(CompilationUnit cu) {
        return (MethodDeclaration)
                cu.findFirst(MethodCallExpr.class).get().resolve().toAst().get();
    }

    @Test
    void resolveInsideDeclarationReachedThroughToAst() throws IOException {
        write("Helper.java", HELPER);
        CompilationUnit cu = parse(
                new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(srcDir)),
                "class Main { void m(Helper h) { h.register(\"a\"); } }");

        MethodCallExpr containsKey =
                registerDeclaration(cu).findFirst(MethodCallExpr.class).get();

        assertEquals(
                "java.util.HashMap.containsKey(java.lang.Object)",
                containsKey.resolve().getQualifiedSignature());
    }

    /** The unit is parsed before the type solver gets its parent: resolution still goes through the root. */
    @Test
    void unitParsedBeforeTheParentIsSetResolvesThroughTheRoot() throws IOException {
        write("Helper.java", HELPER);
        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcDir);
        javaParserTypeSolver.solveType("Helper");
        CompilationUnit cu = parse(
                new CombinedTypeSolver(new ReflectionTypeSolver(), javaParserTypeSolver),
                "class Main { void m(Helper h) { h.register(\"a\"); } }");

        MethodCallExpr containsKey =
                registerDeclaration(cu).findFirst(MethodCallExpr.class).get();

        assertEquals(
                "java.util.HashMap.containsKey(java.lang.Object)",
                containsKey.resolve().getQualifiedSignature());
    }

    /** As with ParserConfiguration, a unit parsed with problems gets no symbol resolver. */
    @Test
    void noSymbolResolverOnUnitWithProblems() throws IOException {
        write(
                "Helper.java",
                "public interface Helper {\n"
                        + "  default void register(String s) { check(s); }\n"
                        + "  private void check(String s) {}\n"
                        + "}\n");
        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(
                srcDir, new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8));
        CompilationUnit cu = parse(
                new CombinedTypeSolver(new ReflectionTypeSolver(), javaParserTypeSolver),
                "class Main { void m(Helper h) { h.register(\"a\"); } }");

        assertFalse(registerDeclaration(cu).findCompilationUnit().get().containsData(Node.SYMBOL_RESOLVER_KEY));
    }

    /** A symbol resolver provided by the configuration of the type solver is kept. */
    @Test
    void symbolResolverOfTheConfigurationIsKept() throws IOException {
        write("Helper.java", HELPER);
        ParserConfiguration solverConfiguration =
                new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17);
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(
                new ReflectionTypeSolver(), new JavaParserTypeSolver(srcDir, solverConfiguration));
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        solverConfiguration.setSymbolResolver(symbolSolver);
        CompilationUnit cu = parse(typeSolver, "class Main { void m(Helper h) { h.register(\"a\"); } }");

        assertEquals(
                symbolSolver,
                registerDeclaration(cu).findCompilationUnit().get().getData(Node.SYMBOL_RESOLVER_KEY));
    }
}
