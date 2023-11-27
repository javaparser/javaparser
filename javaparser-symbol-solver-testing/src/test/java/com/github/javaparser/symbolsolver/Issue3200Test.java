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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3200Test {

    @Test
    public void test0() {
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver cts = new CombinedTypeSolver();
        cts.add(new ReflectionTypeSolver(false));
        config.setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(config);

        String str = "public class Test {\n" +
                "    private void bad() {\n" +
                "        Test test = new Test();\n" +
                "        test.setRunnable(\"\", new Runnable() {\n" +
                "            @Override\n" +
                "            public void run() {\n" +
                "                getContext(Test.this);\n" +
                "            }\n" +
                "        });\n" +
                "    }\n" +
                "\n" +
                "    private void getContext(Test test) {\n" +
                "    }\n" +
                "\n" +
                "    private void setRunnable(String str, Runnable runnable) {\n" +
                "    }\n" +
                "}";
        CompilationUnit cu = StaticJavaParser.parse(str);
        List<MethodCallExpr> mce = cu.findAll(MethodCallExpr.class);
        assertEquals("Test.setRunnable(java.lang.String, java.lang.Runnable)",
                mce.get(0).resolve().getQualifiedSignature());
        assertEquals("Test.getContext(Test)", mce.get(1).resolve().getQualifiedSignature());
    }

    @Test
    public void test1() {
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver cts = new CombinedTypeSolver();
        cts.add(new ReflectionTypeSolver(false));
        config.setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(config);

        String str = "public class Test {\n" +
                "    class Inner { }" +
                "    void getContext(Test test) {  }\n" +
                "    {\n" +
                "        new Inner () {\n" +
                "            {\n" +
                "                getContext(Test.this);\n" +
                "            }\n" +
                "        };\n" +
                "    }\n" +
                "}";
        CompilationUnit cu = StaticJavaParser.parse(str);
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration rmd = mce.resolve();
        String sig = rmd.getQualifiedSignature();
        assertEquals("Test.getContext(Test)", sig);
    }

}

