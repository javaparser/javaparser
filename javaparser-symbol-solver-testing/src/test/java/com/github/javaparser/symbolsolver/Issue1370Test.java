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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * Solving generic types that are of type java.lang.Object
 * @see <a href="https://github.com/javaparser/javaparser/issues/1370">https://github.com/javaparser/javaparser/issues/1370</a>
 */
public class Issue1370Test {

    @Test
    public void test() {
        final String source = String.join(System.lineSeparator(),
                                          "package graph;",
                                          "class Vertex<Data> {",
                                          "    private final Data data;",
                                          "    public Vertex(Data data) { this.data = data; }",
                                          "    public Data getData() { return this.data; }",
                                          "}",
                                          "",
                                          "public class Application {",
                                          "    public static void main(String[] args) {",
                                          "        System.out.println(new Vertex<>(42).getData().equals(42));",
                                          "    }",
                                          "}");

        final JavaParserFacade facade = JavaParserFacade.get(new ReflectionTypeSolver(false));

        StaticJavaParser.parse(source).accept(new VoidVisitorAdapter<Void>() {
            @Override
            public void visit(final MethodCallExpr n, final Void arg) {
                super.visit(n, arg);

                try {
                    System.out.printf("Node: %s, solved Type: %s%n", n, facade.solve(n));
                } catch (RuntimeException e) {
                    e.printStackTrace();
                }
            }
        }, null);
    }
}
