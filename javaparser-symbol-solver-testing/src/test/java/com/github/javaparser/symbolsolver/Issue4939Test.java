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
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * The declarations of a record must be resolved with the type solver of the record, not with the symbol resolver
 * of its compilation unit, which may be missing.
 */
class Issue4939Test {

    /** Parses without any symbol resolver, as a facade user or a type solver does. */
    private static CompilationUnit parseWithoutSymbolResolver(String code) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17))
                .parse(code)
                .getResult()
                .get();
    }

    private static MethodCallExpr firstCall(CompilationUnit cu) {
        return cu.findFirst(MethodCallExpr.class).get();
    }

    private static JavaParserFacade facade() {
        return JavaParserFacade.get(new ReflectionTypeSolver());
    }

    @Test
    void recordAccessor() {
        CompilationUnit cu = parseWithoutSymbolResolver(
                "record Point(int x, int y) {}\n class Main { int m(Point p) { return p.x(); } }");

        assertEquals(
                "Point.x()",
                facade().solve(firstCall(cu)).getCorrespondingDeclaration().getQualifiedSignature());
    }

    @Test
    void recordAccessorWithOverload() {
        CompilationUnit cu = parseWithoutSymbolResolver(
                "record Point(int x, int y) { public int x(int scale) { return x * scale; } }\n"
                        + " class Main { int m(Point p) { return p.x(); } }");

        assertEquals(
                "Point.x()",
                facade().solve(firstCall(cu)).getCorrespondingDeclaration().getQualifiedSignature());
    }

    @Test
    void recordAccessorWithLibraryComponentType() {
        CompilationUnit cu = parseWithoutSymbolResolver("import java.util.List;\n"
                + "record Box(List<String> items) {}\n"
                + " class Main { void m(Box b) { b.items(); } }");

        assertEquals(
                "java.util.List<java.lang.String>",
                facade().getType(firstCall(cu)).describe());
    }

    @Test
    void varargsRecordComponentAccessorReturnsAnArray() {
        CompilationUnit cu =
                parseWithoutSymbolResolver("record R(int... xs) {}\n class Main { void m(R r) { r.xs(); } }");

        assertEquals("int[]", facade().getType(firstCall(cu)).describe());
    }

    @Test
    void explicitVarargsCanonicalConstructorIsNotDuplicated() {
        CompilationUnit cu = parseWithoutSymbolResolver("record R(int... xs) { R(int... xs) { this.xs = xs; } }");

        assertEquals(
                1,
                facade().getTypeDeclaration(
                                cu.findFirst(RecordDeclaration.class).get())
                        .getConstructors()
                        .size());
    }

    /** A record declared in a library is not a JavaParserRecordDeclaration and keeps working. */
    @Test
    void recordAccessorDeclaredInLibrary() {
        CompilationUnit cu = new JavaParser(new ParserConfiguration()
                        .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                        .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false))))
                .parse("class Main { Object m(jdk.net.UnixDomainPrincipal p) { return p.user(); } }")
                .getResult()
                .get();

        assertEquals(
                "jdk.net.UnixDomainPrincipal.user()", firstCall(cu).resolve().getQualifiedSignature());
    }
}
