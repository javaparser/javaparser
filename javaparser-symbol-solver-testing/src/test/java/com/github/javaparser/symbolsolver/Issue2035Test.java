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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.stream.Collectors;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

class Issue2035Test {

    private JavaParser javaParser;

    @BeforeEach
    void setUp() {
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver());
        ParserConfiguration configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        javaParser = new JavaParser(configuration);
    }

    @Test
    void test() {
        String x = "" +
                "class X {\n" +
                "    \n" +
                "    private void a(int a){ }\n" +
                "    private void b(Integer a){ }\n" +
                "    \n" +
                "    private void c(){\n" +
                "        int x=0;\n" +
                "        Integer y=0;\n" +
                "        \n" +
                "        a(x);\n" +
                "        a(y);\n" +
                "        \n" +
                "        b(x);\n" +
                "        b(y);\n" +
                "        \n" +
                "    }\n" +
                "}" +
                "";

        ParseResult<CompilationUnit> parseResult = javaParser.parse(
                ParseStart.COMPILATION_UNIT,
                provider(x)
        );

        parseResult.getResult().ifPresent(compilationUnit -> {
            final List<MethodCallExpr> matches = compilationUnit
                    .findAll(MethodCallExpr.class);

            assumeFalse(matches.isEmpty(), "Cannot attempt resolving types if no matches.");
            matches.forEach(methodCallExpr -> {
                try {
                    methodCallExpr.resolve().getReturnType();
                    methodCallExpr.calculateResolvedType(); //
                } catch (UnsupportedOperationException e) {
                    Assertions.fail("Resolution failed.", e);
                }
            });
        });

    }


    @Test
    void test_int() {
        String x_int = "" +
                "import java.util.*;\n" +
                "\n" +
                "class X {\n" +
                "    \n" +
                "    private void a(){\n" +
                "        ArrayList<String> abc = new ArrayList<>();\n" +
                "        int x = 0; \n" +
                "        abc.get(x);\n" +
                "    }\n" +
                "}" +
                "";

        ParseResult<CompilationUnit> parseResult = javaParser.parse(
                ParseStart.COMPILATION_UNIT,
                provider(x_int)
        );

        parseResult.getResult().ifPresent(compilationUnit -> {
            final List<MethodCallExpr> matches = compilationUnit
                    .findAll(MethodCallExpr.class)
                    .stream()
                    .filter(methodCallExpr -> methodCallExpr.getNameAsString().equals("get"))
                    .collect(Collectors.toList());

            assumeFalse(matches.isEmpty(), "Cannot attempt resolving types if no matches.");
            matches.forEach(methodCallExpr -> {
                try {
                    methodCallExpr.resolve().getReturnType();
                    methodCallExpr.calculateResolvedType();
                } catch (UnsupportedOperationException e) {
                    Assertions.fail("Resolution failed.", e);
                }
            });
        });

    }

    @Test
    void test_Integer() {
        String x_Integer = "" +
                "import java.util.*;\n" +
                "\n" +
                "class X {\n" +
                "    \n" +
                "    private void a(){\n" +
                "        ArrayList<String> abc = new ArrayList<>();\n" +
                "        Integer x = 0; \n" +
                "        abc.get(x);\n" +
                "    }\n" +
                "}" +
                "";

        ParseResult<CompilationUnit> parseResult = javaParser.parse(
                ParseStart.COMPILATION_UNIT,
                provider(x_Integer)
        );

        parseResult.getResult().ifPresent(compilationUnit -> {
            final List<MethodCallExpr> matches = compilationUnit
                    .findAll(MethodCallExpr.class)
                    .stream()
                    .filter(methodCallExpr -> methodCallExpr.getNameAsString().equals("get"))
                    .collect(Collectors.toList());

            assumeFalse(matches.isEmpty(), "Cannot attempt resolving types if no matches.");
            matches.forEach(methodCallExpr -> {
                try {
                    methodCallExpr.resolve().getReturnType();
                    methodCallExpr.calculateResolvedType();
                } catch (UnsupportedOperationException e) {
                    Assertions.fail("Resolution failed.", e);
                }
            });
        });
    }

}
