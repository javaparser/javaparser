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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests resolution of MethodCallExpr with super classes
 *
 * @author Takeshi D. Itoh
 */
class CompilationUnitContextResolutionTest extends AbstractResolutionTest {

    @AfterEach
    void unConfigureSymbolSolver() {
        // unconfigure symbol solver so as not to potentially disturb tests in other classes
        StaticJavaParser.getConfiguration().setSymbolResolver(null);
    }

    // in each case, the name itself doesn't matter -- we just want to assert that StackOverflowError wouldn't occur.

    @Test
    void solveMethodInReceiver() throws IOException {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
            new ReflectionTypeSolver(),
            new JavaParserTypeSolver(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/00_receiver")))));

        CompilationUnit cu = StaticJavaParser.parse(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/00_receiver/main/Main.java"));
        MethodCallExpr mce = Navigator.findMethodCall(cu, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("main.Child.method", actual);
    }

    @Test
    void solveMethodInParent() throws IOException {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
            new ReflectionTypeSolver(),
            new JavaParserTypeSolver(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/01_parent")))));

        CompilationUnit cu = StaticJavaParser.parse(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/01_parent/main/Main.java"));
        MethodCallExpr mce = Navigator.findMethodCall(cu, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("main.Parent.method", actual);
    }

    @Test
    void solveMethodInNested() throws IOException {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
            new ReflectionTypeSolver(),
            new JavaParserTypeSolver(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/02_nested")))));

        CompilationUnit cu = StaticJavaParser.parse(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/02_nested/main/Main.java"));
        MethodCallExpr mce = Navigator.findMethodCall(cu, "method").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("main.Child.method", actual);
    }

    @Test
    void solveSymbol() throws IOException {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
            new ReflectionTypeSolver(),
            new JavaParserTypeSolver(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/03_symbol")))));

        CompilationUnit cu = StaticJavaParser.parse(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/03_symbol/main/Main.java"));
        NameExpr ne = Navigator.findNameExpression(cu, "A").get();
        String actual = ne.resolve().getType().describe();
        assertEquals("main.Clazz.MyEnum", actual);
    }

    @Test
    void solveMyself() throws IOException {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
            new ReflectionTypeSolver(),
            new JavaParserTypeSolver(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/04_reviewComment")))));

        CompilationUnit cu = StaticJavaParser.parse(adaptPath("src/test/resources/CompilationUnitContextResolutionTest/04_reviewComment/main/Main.java"));

        MethodCallExpr mce = Navigator.findMethodCall(cu, "foo").get();
        String actual = mce.resolve().getQualifiedName();
        assertEquals("main.Main.NestedEnum.foo", actual);

        mce = Navigator.findMethodCall(cu, "bar").get();
        actual = mce.resolve().getQualifiedName();
        assertEquals("main.Main.NestedEnum.bar", actual);

        mce = Navigator.findMethodCall(cu, "baz").get();
        actual = mce.resolve().getQualifiedName();
        assertEquals("main.Main.NestedEnum.baz", actual);
    }

}
