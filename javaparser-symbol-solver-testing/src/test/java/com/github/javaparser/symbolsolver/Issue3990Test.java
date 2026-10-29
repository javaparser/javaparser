/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * Symbol resolution of local enum declarations (<a href="https://github.com/javaparser/javaparser/issues/3990">#3990</a>).
 */
class Issue3990Test extends AbstractResolutionTest {

    private static final String CODE = "class X {\n"
            + "  void m() {\n"
            + "    enum E { A, B; int v(){ return 1; } }\n"
            + "    E e = E.A;\n"
            + "    int x = e.v();\n"
            + "    String s = E.A.name();\n"
            + "    switch (e) { case A: break; default: break; }\n"
            + "  }\n"
            + "}\n";

    private final CompilationUnit cu = parse();

    @Test
    void localEnumTypeResolvesToQualifiedName() {
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("E"))
                .get();

        assertEquals("X.E", type.resolve().asReferenceType().getQualifiedName());
    }

    @Test
    void localEnumConstantAccessResolvesToConstant() {
        FieldAccessExpr access = cu.findFirst(FieldAccessExpr.class).get();

        ResolvedValueDeclaration constant = access.resolve();

        assertEquals("A", constant.getName());
        assertEquals("X.E", constant.getType().describe());
    }

    @Test
    void methodDeclaredOnLocalEnumResolves() {
        MethodCallExpr call = cu.findFirst(
                        MethodCallExpr.class, c -> c.getNameAsString().equals("v"))
                .get();

        assertEquals("X.E.v()", call.resolve().getQualifiedSignature());
    }

    @Test
    void methodInheritedFromEnumResolvesOnLocalEnumConstant() {
        MethodCallExpr call = cu.findFirst(
                        MethodCallExpr.class, c -> c.getNameAsString().equals("name"))
                .get();

        assertEquals("java.lang.Enum.name()", call.resolve().getQualifiedSignature());
    }

    @Test
    void switchCaseLabelResolvesToLocalEnumConstant() {
        SwitchEntry entry = cu.findFirst(SwitchEntry.class).get();

        ResolvedEnumConstantDeclaration constant =
                entry.getLabels().get(0).asNameExpr().resolve().asEnumConstant();

        assertEquals("A", constant.getName());
        assertEquals("X.E", constant.getType().describe());
    }

    private CompilationUnit parse() {
        ParserConfiguration config = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        return new JavaParser(config).parse(CODE).getResult().get();
    }
}
