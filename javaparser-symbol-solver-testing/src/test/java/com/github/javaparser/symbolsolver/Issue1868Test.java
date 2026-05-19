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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.nio.file.Path;
import java.util.List;
import org.junit.jupiter.api.Test;

public class Issue1868Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {

        Path testResources = adaptPath("src/test/resources/issue1868");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(testResources));

        StaticJavaParser.setConfiguration(
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));

        String s = """
                class A {
                    public void foo() {
                        toArray(new String[0]);
                    }
                    public void bar() {
                        B b = null;
                        b.toArray(new String[0]);
                    }
                    public <T> T[] toArray(T[] tArray) {
                        // ...
                    }
                }\
                """;

        CompilationUnit cu = StaticJavaParser.parse(s);

        List<MethodCallExpr> mces = cu.findAll(MethodCallExpr.class);

        assertEquals(
                "toArray(new String[0]) resolved to A.toArray",
                "%s resolved to %s".formatted(mces.get(0), mces.get(0).resolve().getQualifiedName()));
        assertEquals(
                "b.toArray(new String[0]) resolved to B.toArray",
                "%s resolved to %s".formatted(mces.get(1), mces.get(1).resolve().getQualifiedName()));
    }
}
