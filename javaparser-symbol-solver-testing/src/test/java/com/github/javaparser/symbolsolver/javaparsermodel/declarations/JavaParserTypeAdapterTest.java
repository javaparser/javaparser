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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Test;

/**
 * A type declaration is resolved with its own type solver, even when its compilation unit has no symbol resolver.
 */
class JavaParserTypeAdapterTest {

    private static CompilationUnit parseWithoutSymbolResolver(String code) {
        return new JavaParser(new ParserConfiguration()).parse(code).getResult().get();
    }

    private static JavaParserClassDeclaration declaration(ClassOrInterfaceDeclaration node) {
        return new JavaParserClassDeclaration(node, new ReflectionTypeSolver());
    }

    @Test
    void containerTypeOfNestedClass() {
        CompilationUnit cu = parseWithoutSymbolResolver("class Outer { class Inner {} }");

        assertEquals(
                "Outer",
                declaration(cu.findAll(ClassOrInterfaceDeclaration.class).get(1))
                        .containerType()
                        .get()
                        .getQualifiedName());
    }

    @Test
    void declaredAnnotations() {
        CompilationUnit cu = parseWithoutSymbolResolver("@Deprecated class A {}");

        assertEquals(
                "java.lang.Deprecated",
                declaration(cu.findFirst(ClassOrInterfaceDeclaration.class).get()).getDeclaredAnnotations().stream()
                        .map(ResolvedAnnotationDeclaration::getQualifiedName)
                        .collect(Collectors.joining()));
    }
}
