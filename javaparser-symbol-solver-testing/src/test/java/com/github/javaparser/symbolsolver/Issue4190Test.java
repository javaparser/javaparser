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
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

/**
 * A package only makes its types visible, not its subpackages (JLS 6.5.2, 7.5.2), and a qualified name
 * that cannot be found must not be retried with its leading segments dropped. Otherwise
 * {@code impl.RecordServiceImpl}, read from the unresolvable superclass
 * {@code com.example.core.service.impl.RecordServiceImpl}, was taken for the declaring class itself
 * through {@code import com.example.service.*}, which made the class its own ancestor.
 */
class Issue4190Test extends AbstractSymbolResolutionTest {

    private final Path resources = adaptPath("src/test/resources/issue4190");

    private JavaParser parser() {
        CombinedTypeSolver typeSolver =
                new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(resources));
        return new JavaParser(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)));
    }

    private CompilationUnit parse(String code) {
        return parser().parse(code).getResult().get();
    }

    private static String fieldType(CompilationUnit cu, String fieldName) {
        return cu.findFirst(
                        FieldDeclaration.class,
                        f -> f.getVariable(0).getNameAsString().equals(fieldName))
                .get()
                .getElementType()
                .resolve()
                .describe();
    }

    private CompilationUnit parseRecordServiceImpl() throws IOException {
        return parser().parse(resources.resolve("com/example/service/impl/RecordServiceImpl.java"))
                .getResult()
                .get();
    }

    @Test
    void unresolvableSuperclassIsNotTakenForTheClassItself() throws IOException {
        ResolvedReferenceTypeDeclaration declaration = parseRecordServiceImpl()
                .findFirst(ClassOrInterfaceDeclaration.class)
                .get()
                .resolve();

        assertThrows(UnsolvedSymbolException.class, () -> declaration.asClass().getSuperClass());
    }

    @Test
    void missingSupertypeOfAnAnonymousClassIsReportedInsteadOfOverflowingTheStack() throws IOException {
        MethodDeclaration after =
                parseRecordServiceImpl().findFirst(MethodDeclaration.class).get();

        // CreateProcessor, the supertype of the anonymous class, is not part of the sources.
        assertThrows(UnsolvedSymbolException.class, () -> after.resolve().getQualifiedName());
    }

    @Test
    void unresolvableQualifiedSuperclassIsNotRetriedWithoutItsLeadingSegments() {
        CompilationUnit cu = parse("package p;\nclass X extends unknown.Outer.Inner {}");
        ResolvedReferenceTypeDeclaration declaration =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get().resolve();

        assertThrows(UnsolvedSymbolException.class, () -> declaration.asClass().getSuperClass());
    }

    @Test
    void importOnDemandDoesNotExposeSubpackages() {
        CompilationUnit cu = parse("package q;\nimport p.*;\nclass X { sub.A a; }");

        assertThrows(UnsolvedSymbolException.class, () -> fieldType(cu, "a"));
    }

    @Test
    void importOnDemandStillExposesMemberTypes() {
        CompilationUnit cu = parse("package q;\nimport p.*;\nclass X { Outer.Inner i; }");

        assertEquals("p.Outer.Inner", fieldType(cu, "i"));
    }

    @Test
    void currentPackageDoesNotExposeSubpackages() {
        CompilationUnit cu = parse("package p;\nclass X { sub.A a; }");

        assertThrows(UnsolvedSymbolException.class, () -> fieldType(cu, "a"));
    }

    @Test
    void currentPackageStillExposesMemberTypes() {
        CompilationUnit cu = parse("package p;\nclass X { Outer.Inner i; }");

        assertEquals("p.Outer.Inner", fieldType(cu, "i"));
    }

    @Test
    void fullyQualifiedNameIsStillResolved() {
        CompilationUnit cu = parse("package q;\nclass X { p.sub.A a; }");

        assertEquals("p.sub.A", fieldType(cu, "a"));
    }
}
