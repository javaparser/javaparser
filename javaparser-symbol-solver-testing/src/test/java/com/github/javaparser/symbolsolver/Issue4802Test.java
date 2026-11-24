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

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

class Issue4802Test extends AbstractSymbolResolutionTest {

    private static MethodCallExpr findCall(String code, String name) {
        ParserConfiguration config = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = new JavaParser(config).parse(code).getResult().get();
        return cu.findFirst(MethodCallExpr.class, call -> call.getNameAsString().equals(name))
                .get();
    }

    @Test
    void resolveChainedCallAfterComputeIfAbsentWithDiamond() {
        String code = "import java.util.*;\n"
                + "class Scratch {\n"
                + "    void foo() {\n"
                + "        Map<Long, List<String>> map = new HashMap<>();\n"
                + "        map.computeIfAbsent(0L, unused -> new ArrayList<>()).add(\"\");\n"
                + "    }\n"
                + "}\n";

        MethodCallExpr add = findCall(code, "add");
        assertEquals("java.util.List.add(E)", add.resolve().getQualifiedSignature());
        assertEquals("boolean", add.calculateResolvedType().describe());

        MethodCallExpr computeIfAbsent = findCall(code, "computeIfAbsent");
        assertEquals(
                "java.util.List<java.lang.String>",
                computeIfAbsent.calculateResolvedType().describe());
    }

    @Test
    void resolvePutWithDiamondArgument() {
        String code = "import java.util.*;\n"
                + "class Scratch {\n"
                + "    void foo() {\n"
                + "        Map<Long, List<String>> map = new HashMap<>();\n"
                + "        map.put(0L, new ArrayList<>());\n"
                + "    }\n"
                + "}\n";

        MethodCallExpr put = findCall(code, "put");
        assertEquals("java.util.Map.put(K, V)", put.resolve().getQualifiedSignature());
        assertEquals(
                "java.util.List<java.lang.String>", put.calculateResolvedType().describe());
    }

    @Test
    void resolveBlockLambdaWithDiamondReturn() {
        String code = "import java.util.*;\n"
                + "class Scratch {\n"
                + "    void foo() {\n"
                + "        Map<Long, List<String>> map = new HashMap<>();\n"
                + "        map.computeIfAbsent(0L, unused -> { return new ArrayList<>(); }).add(\"\");\n"
                + "    }\n"
                + "}\n";

        MethodCallExpr add = findCall(code, "add");
        assertEquals("java.util.List.add(E)", add.resolve().getQualifiedSignature());
    }

    @Test
    void resolveMultipleDiamondArgumentsWithoutConflictingTypeVariables() {
        String code = "import java.util.*;\n"
                + "class Scratch {\n"
                + "    static <T, U> T pickFirst(List<T> a, T first, List<U> b, U second) { return first; }\n"
                + "    void foo() {\n"
                + "        pickFirst(new ArrayList<>(), \"s\", new ArrayList<>(), 1);\n"
                + "    }\n"
                + "}\n";

        MethodCallExpr pickFirst = findCall(code, "pickFirst");
        assertEquals("java.lang.String", pickFirst.calculateResolvedType().describe());
    }

    @Test
    void resolveSubclassExtendingRawGenericType() {
        String code = "import java.util.*;\n"
                + "class Scratch {\n"
                + "    static class RawSub extends ArrayList {}\n"
                + "    void foo() {\n"
                + "        Map<Long, List<String>> map = new HashMap<>();\n"
                + "        map.put(0L, new RawSub());\n"
                + "    }\n"
                + "}\n";

        MethodCallExpr put = findCall(code, "put");
        assertEquals("java.util.Map.put(K, V)", put.resolve().getQualifiedSignature());
        assertEquals(
                "java.util.List<java.lang.String>", put.calculateResolvedType().describe());
    }

    @Test
    void resolveNestedListAddWithDiamond() {
        String code = "import java.util.*;\n"
                + "class Scratch {\n"
                + "    void foo() {\n"
                + "        List<List<String>> lists = new ArrayList<>();\n"
                + "        lists.add(new ArrayList<>());\n"
                + "    }\n"
                + "}\n";

        MethodCallExpr add = findCall(code, "add");
        assertEquals("java.util.List.add(E)", add.resolve().getQualifiedSignature());
    }
}
