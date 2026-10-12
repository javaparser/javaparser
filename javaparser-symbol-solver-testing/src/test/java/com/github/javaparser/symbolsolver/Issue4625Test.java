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
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue4625Test extends AbstractResolutionTest {

    @Test
    void methodReferenceAsArgumentOfGenericMethodDoesNotBindTypeVariableToItself() {
        String code = "import java.util.Collections;\n"
                + "import java.util.Map;\n"
                + "import java.util.Set;\n"
                + "import java.util.stream.Collectors;\n"
                + "import java.util.stream.Stream;\n"
                + "public class Category {\n"
                + "  public static final Map<Integer, Set<String>> unmodifiableFromStream4 =\n"
                + "    Stream.of(\"first\", \"second\", \"second\", \"thirteen\", \"thirteen\", \"thirteen\")\n"
                + "      .collect(\n"
                + "        Collectors.collectingAndThen(\n"
                + "          Collectors.groupingBy(\n"
                + "            String::length, Collectors.toSet()\n"
                + "          ),\n"
                + "          Collections::unmodifiableMap\n"
                + "        )\n"
                + "      );\n"
                + "}\n";
        ParserConfiguration config = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_18)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = new JavaParser(config).parse(code).getResult().get();

        assertEquals(
                "java.util.stream.Stream.collect(java.util.stream.Collector<? super T, A, R>)",
                resolveMethodCall(cu, "collect"));
        assertEquals(
                "java.util.stream.Collectors.collectingAndThen(java.util.stream.Collector<T, A, R>, java.util.function.Function<R, RR>)",
                resolveMethodCall(cu, "collectingAndThen"));
        assertEquals(
                "java.util.Collections.unmodifiableMap(java.util.Map<? extends K, ? extends V>)",
                cu.findFirst(MethodReferenceExpr.class, mre -> mre.getIdentifier()
                                .equals("unmodifiableMap"))
                        .get()
                        .resolve()
                        .getQualifiedSignature());
    }

    private String resolveMethodCall(CompilationUnit cu, String name) {
        return cu.findFirst(MethodCallExpr.class, mce -> mce.getNameAsString().equals(name))
                .get()
                .resolve()
                .getQualifiedSignature();
    }
}
