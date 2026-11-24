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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Issue #5254: the types of the {@code implements} clause of an enum and of the {@code extends} clause of an
 * interface must not be resolved against the member types of the declaration (JLS 6.3), they are resolved from
 * the enclosing scope. The expected ancestors are the ones reported by javac 17 for the same sources.
 */
class Issue5254Test {

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        JavaParserFacade.clearInstances();
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        javaParser = new JavaParser(configuration);
    }

    private CompilationUnit parse(String code) {
        return javaParser.parse(code).getResult().get();
    }

    private static ResolvedReferenceTypeDeclaration declaration(CompilationUnit cu, String simpleName) {
        return cu.findFirst(TypeDeclaration.class, t -> t.getNameAsString().equals(simpleName))
                .get()
                .resolve();
    }

    private static List<String> ancestors(CompilationUnit cu, String simpleName) {
        return declaration(cu, simpleName).getAncestors().stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toList());
    }

    private static final String MEMBER_WITH_THE_SAME_NAME = "interface I { default int f() { return 1; } }\n"
            + "enum O implements I { A; interface I {} }\n"
            + "interface P extends I { interface I {} }\n"
            + "class M { int m() { return O.A.f(); } }";

    @Test
    void enumImplementsTheTopLevelTypeRatherThanItsMemberType() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        assertEquals(Arrays.asList("java.lang.Enum<O>", "I"), ancestors(cu, "O"));
    }

    @Test
    void interfaceExtendsTheTopLevelTypeRatherThanItsMemberType() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        assertEquals(Arrays.asList("I"), ancestors(cu, "P"));
    }

    @Test
    void methodInheritedFromTheTopLevelTypeIsResolved() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        MethodCallExpr call = cu.findFirst(MethodCallExpr.class).get();
        assertEquals("I.f()", call.resolve().getQualifiedSignature());
    }

    @Test
    void enumIsAssignableToTheTopLevelType() {
        CompilationUnit cu = parse(MEMBER_WITH_THE_SAME_NAME);

        ResolvedReferenceTypeDeclaration topLevel = cu.getType(0).resolve();
        assertTrue(topLevel.isAssignableBy(declaration(cu, "O")));
    }

    @Test
    void typesDeclaredInTheEnclosingTypeAreStillResolved() {
        CompilationUnit cu = parse("class Outer { interface X {} enum E implements X { A } interface Y extends X {} }");

        assertEquals(Arrays.asList("java.lang.Enum<Outer.E>", "Outer.X"), ancestors(cu, "E"));
        assertEquals(Arrays.asList("Outer.X"), ancestors(cu, "Y"));
    }

    @Test
    void typesDeclaredInTheEnclosingBlockAreStillResolved() {
        CompilationUnit cu =
                parse("class Top { void m() { interface X {} enum E implements X { A } interface Y extends X {} } }");
        String x = declaration(cu, "X").getQualifiedName();

        List<ResolvedReferenceType> enumAncestors = declaration(cu, "E").getAncestors();
        assertEquals(2, enumAncestors.size());
        assertEquals(x, enumAncestors.get(1).getQualifiedName());
        List<ResolvedReferenceType> interfaceAncestors = declaration(cu, "Y").getAncestors();
        assertEquals(1, interfaceAncestors.size());
        assertEquals(x, interfaceAncestors.get(0).getQualifiedName());
    }

    @Test
    void qualifiedAndParameterizedTypesAreStillResolved() {
        CompilationUnit cu = parse(
                "interface O<T> extends java.util.Comparator<T> {}\n" + "enum E implements java.io.Serializable { A }");

        assertEquals(Arrays.asList("java.util.Comparator<T>"), ancestors(cu, "O"));
        assertEquals(Arrays.asList("java.lang.Enum<E>", "java.io.Serializable"), ancestors(cu, "E"));
    }
}
