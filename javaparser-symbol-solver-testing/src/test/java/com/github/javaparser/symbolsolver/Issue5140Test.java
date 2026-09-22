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
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * A type name qualified by another type resolves against the member types of that type. Imports are
 * not transitive -- neither the static ones (JLS 7.5.3, 7.5.4) nor the ordinary ones (JLS 7.5.1,
 * 7.5.2) -- so the ones written in the file that declares the receiver type do not add member types
 * to it: {@code Mid.Nested} is a compile error when {@code Mid.java} merely imports {@code Nested}
 * from elsewhere.
 */
public class Issue5140Test extends AbstractSymbolResolutionTest {

    private CompilationUnit cu;

    @BeforeEach
    void parseOuter() throws IOException {
        Path issueResourcesPath = adaptPath("src/test/resources/issue5140");
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(issueResourcesPath));
        cu = new JavaParser(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver)))
                .parse(issueResourcesPath.resolve("qq/Outer.java"))
                .getResult()
                .get();
    }

    @Test
    void aNestedTypeIsNotReachedThroughThatFilesStaticImports() {
        ClassOrInterfaceType type = typeIn("viaObjectCreation");

        assertThrows(UnsolvedSymbolException.class, type::resolve);
    }

    @Test
    void aTypeUseIsNotReachedThroughThatFilesStaticImports() {
        ClassOrInterfaceType type = typeIn("viaTypeUse");

        assertThrows(UnsolvedSymbolException.class, type::resolve);
    }

    @Test
    void aNestedTypeIsNotReachedThroughThatFilesOrdinaryImports() {
        ClassOrInterfaceType type = typeIn("viaOrdinaryImport");

        assertThrows(UnsolvedSymbolException.class, type::resolve);
    }

    @Test
    void aNestedTypeOfTheTypeItselfStillResolves() {
        ClassOrInterfaceType type = typeIn("nestedTypeOfTheTypeItself");

        assertEquals("qq.Sink.Nested", type.resolve().describe());
    }

    @Test
    void aNestedTypeInheritedFromAnAncestorStillResolves() {
        // What the member lookup must keep doing, and the reason the resolution went through the
        // context in the first place.
        ClassOrInterfaceType type = typeIn("nestedTypeInheritedFromAnAncestor");

        assertEquals("qq.Base.Inherited", type.resolve().describe());
    }

    private ClassOrInterfaceType typeIn(String methodName) {
        MethodDeclaration method = cu.findAll(MethodDeclaration.class).stream()
                .filter(it -> it.getNameAsString().equals(methodName))
                .findFirst()
                .get();
        return method.findAll(ObjectCreationExpr.class).stream()
                .map(ObjectCreationExpr::getType)
                .findFirst()
                .orElseGet(() -> method.findAll(ClassOrInterfaceType.class).stream()
                        .filter(it -> it.getScope().isPresent())
                        .findFirst()
                        .get());
    }
}
