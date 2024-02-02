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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3878Test {

    @BeforeEach
    void setup() {
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(new ReflectionTypeSolver());
        StaticJavaParser.getParserConfiguration().setSymbolResolver(symbolSolver);
    }

    @Test
    void resolve_method_reference_in_ObjectCreationExpr() {
        String code = "package test;\n" +
                "import java.util.function.Consumer;\n" +
                "\n" +
                "class A {\n" +
                "A(Consumer<Integer> f) {}\n" +
                "void bar(int i) {}\n" +
                "void foo() { new A(this::bar); }\n" +
                "}";
        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodReferenceExpr expr = cu.findFirst(MethodReferenceExpr.class).get();

        ResolvedMethodDeclaration decl = expr.resolve();

        assertEquals("test.A.bar(int)", decl.getQualifiedSignature());
    }
}
