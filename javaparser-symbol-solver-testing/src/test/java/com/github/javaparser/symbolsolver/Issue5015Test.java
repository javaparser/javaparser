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
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Reproducer for <a href="https://github.com/javaparser/javaparser/issues/5015">#5015</a>.
 *
 * <p>A method call in a file parsed by the user is resolved, and the visitor then walks into the
 * declaration returned by {@code toAst()}. That declaration comes from a compilation unit that
 * {@link JavaParserTypeSolver} parsed with its own {@link ParserConfiguration}. Resolving a call
 * inside it only works when that configuration carries a symbol resolver, as explained in
 * <a href="https://github.com/javaparser/javaparser/issues/4286">#4286</a>.
 */
public class Issue5015Test extends AbstractResolutionTest {

    private static final String CALLEE = ""
            + "import java.util.HashMap;\n"
            + "\n"
            + "public class Callee {\n"
            + "    private HashMap<String, String> cache = new HashMap<>();\n"
            + "\n"
            + "    public void register(String key) {\n"
            + "        cache.containsKey(key);\n"
            + "    }\n"
            + "}\n";

    private static final String CALLER = ""
            + "public class Caller {\n"
            + "    void run(Callee callee) {\n"
            + "        callee.register(\"key\");\n"
            + "    }\n"
            + "}\n";

    @TempDir
    Path srcDir;

    @BeforeEach
    void writeCallee() throws IOException {
        Files.write(srcDir.resolve("Callee.java"), CALLEE.getBytes());
    }

    @Test
    void callInsideDeclarationFromDefaultTypeSolverCannotBeResolved() {
        MethodCallExpr containsKey = findContainsKeyThroughToAst(new JavaParserTypeSolver(srcDir));

        IllegalStateException exception = assertThrows(IllegalStateException.class, containsKey::resolve);
        assertEquals(
                "Symbol resolution not configured: to configure consider setting a SymbolResolver in the ParserConfiguration",
                exception.getMessage());
    }

    @Test
    void callInsideDeclarationFromConfiguredTypeSolverCanBeResolved() {
        ParserConfiguration typeSolverConfiguration = new ParserConfiguration();
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(srcDir, typeSolverConfiguration);
        MethodCallExpr containsKey = findContainsKeyThroughToAst(typeSolver, typeSolverConfiguration);

        assertEquals(
                "java.util.HashMap.containsKey(java.lang.Object)",
                containsKey.resolve().getQualifiedSignature());
    }

    private MethodCallExpr findContainsKeyThroughToAst(JavaParserTypeSolver typeSolver) {
        return findContainsKeyThroughToAst(typeSolver, null);
    }

    /**
     * Resolves {@code callee.register("key")} in a caller parsed with a symbol resolver, then returns
     * the {@code cache.containsKey(key)} call found in the declaration given by {@code toAst()}.
     * When {@code typeSolverConfiguration} is not null, it receives the same symbol resolver.
     */
    private MethodCallExpr findContainsKeyThroughToAst(
            JavaParserTypeSolver typeSolver, ParserConfiguration typeSolverConfiguration) {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), typeSolver);
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(combinedTypeSolver);
        if (typeSolverConfiguration != null) {
            typeSolverConfiguration.setSymbolResolver(symbolSolver);
        }
        ParserConfiguration callerConfiguration = new ParserConfiguration().setSymbolResolver(symbolSolver);
        CompilationUnit caller =
                new JavaParser(callerConfiguration).parse(CALLER).getResult().get();

        MethodDeclaration register = (MethodDeclaration)
                caller.findFirst(MethodCallExpr.class).get().resolve().toAst().get();
        return register.findFirst(MethodCallExpr.class).get();
    }
}
