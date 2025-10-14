/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.junit.jupiter.api.Test;

class AnonymousOuterLookupTest {

    private CompilationUnit parse(String code) {
        CombinedTypeSolver solver = new CombinedTypeSolver(new ReflectionTypeSolver());
        ParserConfiguration cfg = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(solver));
        return new JavaParser(cfg).parse(code).getResult().orElseThrow(() -> new AssertionError("Parse failed"));
    }

    private static MethodCallExpr firstCallNamed(CompilationUnit cu, String name) {
        return cu.findAll(MethodCallExpr.class).stream()
                .filter(e -> e.getNameAsString().equals(name))
                .findFirst()
                .orElseThrow(() -> new AssertionError("call '" + name + "' not found"));
    }

    // --- Positives (instance context): should resolve via enclosing instance ---

    /**
     * Anonymous class inside instance method: unqualified call resolves to outer instance method.
     */
    @Test
    void resolves_in_instance_method_via_anonymous() {
        String code = ""
                + "import java.util.concurrent.Callable;\n"
                + "class T {\n"
                + "  String m(String k){ return \"ok\"; }\n"
                + "  String go(String key) throws Exception {\n"
                + "    return new Callable<String>(){\n"
                + "      public String call(){ return m(key); }\n"
                + "    }.call();\n"
                + "  }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = firstCallNamed(cu, "m");
        ResolvedMethodDeclaration r = call.resolve();
        assertEquals("T", r.declaringType().getQualifiedName());
        assertEquals("m", r.getName());
        assertEquals("java.lang.String", r.getParam(0).describeType());
    }

    /**
     * Multiple enclosing instances: walk out to A#m.
     */
    @Test
    void resolves_through_multiple_enclosing_instances() {
        String code = ""
                + "class A {\n"
                + "  String m(String s){ return \"A\"; }\n"
                + "  class B {\n"
                + "    class C {\n"
                + "      String go(String k){ class D{ String x(){ return m(k); } } return new D().x(); }\n"
                + "    }\n"
                + "  }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = firstCallNamed(cu, "m");
        ResolvedMethodDeclaration r = call.resolve();
        assertEquals("A", r.declaringType().getQualifiedName());
    }

    // --- Negatives (static context): must NOT resolve without explicit receiver ---

    /**
     * Anonymous class inside static method: unqualified call must throw.
     */
    @Test
    void does_not_resolve_in_static_method_anonymous_unqualified() {
        String code = ""
                + "import java.util.concurrent.Callable;\n"
                + "class T {\n"
                + "  String m(String k){ return \"ok\"; }\n"
                + "  static String go(String key) throws Exception {\n"
                + "    return new Callable<String>(){\n"
                + "      public String call(){ return m(key); }\n"
                + "    }.call();\n"
                + "  }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = firstCallNamed(cu, "m");
        assertThrows(RuntimeException.class, call::resolve); // UnsolvedSymbolException is a RuntimeException
    }

    /**
     * Local class inside static method: unqualified call must throw.
     */
    @Test
    void does_not_resolve_local_class_in_static_method() {
        String code = ""
                + "class T {\n"
                + "  String m(String k){ return \"ok\"; }\n"
                + "  static String go(String key) {\n"
                + "    class L { String x(){ return m(key); } }\n"
                + "    return new L().x();\n"
                + "  }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = firstCallNamed(cu, "m");
        assertThrows(RuntimeException.class, call::resolve);
    }

    /**
     * Lambda inside static method: unqualified call must throw.
     */
    @Test
    void does_not_resolve_lambda_in_static_method() {
        String code = ""
                + "import java.util.function.Supplier;\n"
                + "class T {\n"
                + "  String m(String k){ return \"ok\"; }\n"
                + "  static String go(String key) {\n"
                + "    Supplier<String> s = () -> m(key);\n"
                + "    return s.get();\n"
                + "  }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = firstCallNamed(cu, "m");
        assertThrows(RuntimeException.class, call::resolve);
    }

    // --- Static with explicit receiver: should resolve ---

    @Test
    void resolves_in_static_with_explicit_receiver() {
        String code = ""
                + "class T {\n"
                + "  String m(String k){ return \"ok\"; }\n"
                + "  static String go(String key) {\n"
                + "    return new T().m(key);\n"
                + "  }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = firstCallNamed(cu, "m");
        ResolvedMethodDeclaration r = call.resolve();
        assertEquals("T", r.declaringType().getQualifiedName());
    }

    @Test
    void resolves_method_in_anonymous_class_with_guava_reflection_solver() throws Exception {
        String code = ""
                + "import com.google.common.cache.Cache;\n"
                + "import com.google.common.cache.CacheBuilder;\n"
                + "import java.util.concurrent.Callable;\n"
                + "\n"
                + "class TestClass {\n"
                + "    Cache<String, String> cache = CacheBuilder.newBuilder().build(); // resolved as reflection or javassist declaration\n"
                + "\n"
                + "    String getByAnnoClass(String key) throws Exception {\n"
                + "        return cache.get(key, new TraceCallable<>(new Callable<String>() {\n"
                + "            @Override\n"
                + "            public String call() {\n"
                + "                return actuallyGet(key);\n"
                + "            }\n"
                + "        }));\n"
                + "    }\n"
                + "\n"
                + "    String actuallyGet(String key) {\n"
                + "        return null;\n"
                + "    }\n"
                + "\n"
                + "    static class TraceCallable<T> implements Callable<T> {\n"
                + "        private final Callable<T> target;\n"
                + "\n"
                + "        TraceCallable(Callable<T> target) {\n"
                + "            this.target = target;\n"
                + "        }\n"
                + "\n"
                + "        @Override\n"
                + "        public T call() throws Exception {\n"
                + "            return target.call();\n"
                + "        }\n"
                + "    }\n"
                + "}\n";

        String m2Repo = System.getProperty("user.home") + "/.m2/repository/com/google/guava/guava";
        String latestVersion = Files.list(Paths.get(m2Repo))
                .filter(Files::isDirectory)
                .map(p -> p.getFileName().toString())
                .sorted()
                .reduce((first, second) -> second)
                .orElseThrow(() -> new RuntimeException("Guava not found in ~/.m2 repository"));
        String guavaJarPath = m2Repo + "/" + latestVersion + "/guava-" + latestVersion + ".jar";

        SymbolResolver symbolResolver = new JavaSymbolSolver(
                new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(guavaJarPath)));
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(symbolResolver);
        CompilationUnit cu = new JavaParser(config).parse(code).getResult().get();

        cu.findAll(MethodCallExpr.class).stream()
                .filter(e -> "actuallyGet".equals(e.getNameAsString()))
                .forEach(expr -> {
                    try {
                        System.out.println(">>> resolving MethodCallExpr: " + expr);
                        ResolvedMethodDeclaration rmd = expr.resolve();
                        System.out.println("<<< MethodDeclaration resolved: " + rmd);
                        assertEquals("TestClass", rmd.declaringType().getClassName());
                        assertEquals("actuallyGet", rmd.getName());
                        assertEquals(1, rmd.getNumberOfParams());
                    } catch (Exception e) {
                        e.printStackTrace();
                        fail("Resolution failed: " + e.getMessage());
                    }
                });
    }
}
