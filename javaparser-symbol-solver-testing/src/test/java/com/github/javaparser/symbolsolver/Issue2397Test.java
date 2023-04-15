/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue2397Test extends AbstractSymbolResolutionTest {

    @Test
    public void testProvided1() {
        String sourceCode = "static final class ConstantFuture<T> implements Future<T> {\n" +
                "        private final T value;\n" +
                "      \n" +
                "        @Override\n" +
                "        public T get() {\n" +
                "            return value;\n" +
                "        }\n" +
                "}";
        testIssue(sourceCode);
    }

    @Test
    public void testProvided2() {
        String sourceCode = "class A {\n" +
                "  public static <T> T[] toArray(final T... items) {\n" +
                "    return items;\n" +
                "  }\n" +
                "}";
        testIssue(sourceCode);
    }

    public void testIssue(String sourceCode) {
        TypeSolver solver = new ReflectionTypeSolver();
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(solver));
        JavaParser parser = new JavaParser(parserConfiguration);

        ParseResult<CompilationUnit> cu = parser.parse(sourceCode);
        cu.ifSuccessful( c -> c.accept(new VoidVisitorAdapter<Void>() {
            @Override
            public void visit(ClassOrInterfaceType classOrInterfaceType, Void arg) {
                super.visit(classOrInterfaceType, arg);

                ResolvedType resolved = classOrInterfaceType.resolve();
                assertTrue(resolved.isTypeVariable());
            }
        }, null));
    }

}
