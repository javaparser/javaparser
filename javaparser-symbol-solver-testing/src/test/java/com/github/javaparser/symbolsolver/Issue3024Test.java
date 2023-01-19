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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3024Test extends AbstractResolutionTest {


    @Test
    public void test() {
        StaticJavaParser.getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit parse = StaticJavaParser.parse("public class Test {\n" +
                "\n" +
                "    public static Test getInstance() {\n" +
                "        return new Test();\n" +
                "    }\n" +
                "\n" +
                "    public void validateBean() {\n" +
                "        Test.getInstance().new InnerClass();\n" +
                "    }\n" +
                "\n" +
                "    public class InnerClass {\n" +
                "        private boolean hasErrors;\n" +
                "    }\n" +
                "}");

        List<MethodCallExpr> methodCallExprList = parse.findAll(MethodCallExpr.class);
        for (MethodCallExpr methodCallExpr : methodCallExprList) {
            assertEquals("Test.getInstance",methodCallExpr.resolve().getQualifiedName());;
        }
    }

}
