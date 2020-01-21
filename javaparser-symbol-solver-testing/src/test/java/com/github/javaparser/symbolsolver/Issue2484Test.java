/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;


/**
 * "SymbolResolver on MethodCallExpr fails if method parameter is of kind Class&lt;? extends y&gt;"
 *
 * @see <a href="https://github.com/javaparser/javaparser/issues/2484">https://github.com/javaparser/javaparser/issues/2484</a>
 */
public class Issue2484Test extends AbstractSymbolResolutionTest {

    private JavaParser javaParser;

    @BeforeEach
    void setUp() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        javaParser = new JavaParser(configuration);
    }

    @Test
    public void test() {
        String x = "public class MyClass {\n" +
            "    private Ibaz m_something;\n" +
            "\n" +
            "    public interface Ibaz {\n" +
            "    }\n" +
            "    \n" +
            "    public void foo(Class<? extends Ibaz> clazz) {\n" +
            "    }\n" +
            "    \n" +
            "    protected void bar() {\n" +
            "        foo(null); // this works\n" +
            "        foo(Ibaz.class); // this works\n" +
            "        foo(m_something.getClass()); // this doesn't work\n" +
            "    }\n" +
            "}";

        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(x));
        assumeTrue(result.isSuccessful());

        result.ifSuccessful(compilationUnit -> {
            List<MethodCallExpr> methodCallExprs = compilationUnit.findAll(MethodCallExpr.class);
            assertEquals(4, methodCallExprs.size());

            for (int i = 0; i < methodCallExprs.size(); i++) {
//                if(i==2) {continue;}
                MethodCallExpr methodCallExpr = methodCallExprs.get(i);
                System.out.println();
                System.out.println("methodCallExpr (" + i + ") = " + methodCallExpr);
                System.out.println("methodCallExpr.resolve() = " + methodCallExpr.resolve());
                System.out.println("methodCallExpr.calculateResolvedType() = " + methodCallExpr.calculateResolvedType());
                System.out.println();
            }

        });
    }

}
