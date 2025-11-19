/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue4668Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = "package com.example.test;\n" + "public class ThisExprTester {\n"
                + "    Test test;\n"
                + "    void getClasses() {\n"
                + "        class innerClass {\n"
                + "            public void test() {\n"
                + "                ThisExprTester.this.test.test();\n"
                + "            }\n"
                + "        }\n"
                + "    }\n"
                + "}\n"
                + "class Test { void test() {} }";
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = StaticJavaParser.parse(code);

        FieldAccessExpr fae = cu.findFirst(FieldAccessExpr.class).orElseThrow(null);
        assertEquals("com.example.test.Test", fae.calculateResolvedType().describe());
        assertEquals(
                "com.example.test.ThisExprTester",
                fae.getScope().calculateResolvedType().describe());
    }
}
