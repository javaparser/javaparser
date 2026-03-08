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

package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import java.util.Optional;
import org.junit.jupiter.api.Test;

public class Issue4703Test {
    @Test
    void ecisResolutionTest() {
        String clazz = "public class Test {\n" + "    public Test(Test test, int... values) {\n"
                + "        System.out.println(test);\n"
                + "        System.out.println(values);\n"
                + "    }\n"
                + "    public Test(int... values) {\n"
                + "        this(null, values);\n"
                + "    }\n"
                + "}";
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        final CompilationUnit cu = StaticJavaParser.parse(clazz);
        final List<ConstructorDeclaration> all = cu.findAll(ConstructorDeclaration.class);
        for (ConstructorDeclaration cd : all) System.out.println(cd.getSignature());
        final Optional<ExplicitConstructorInvocationStmt> ecis = cu.findFirst(ExplicitConstructorInvocationStmt.class);
        assertEquals("Test(Test, int...)", ecis.get().resolve().getSignature());
    }

    @Test
    void specificEcisResolutionTest() {
        String clazz = "public class Test {\n" + "    public Test(Test test, int... values) {\n"
                + "        System.out.println(test);\n"
                + "        System.out.println(values);\n"
                + "    }\n"
                + "    public Test(int... values) {\n"
                + "        this(new Test(), values);\n"
                + "    }\n"
                + "}";
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        final CompilationUnit cu = StaticJavaParser.parse(clazz);
        final List<ConstructorDeclaration> all = cu.findAll(ConstructorDeclaration.class);
        for (ConstructorDeclaration cd : all) System.out.println(cd.getSignature());
        final Optional<ExplicitConstructorInvocationStmt> ecis = cu.findFirst(ExplicitConstructorInvocationStmt.class);
        assertEquals("Test(Test, int...)", ecis.get().resolve().getSignature());
    }
}
