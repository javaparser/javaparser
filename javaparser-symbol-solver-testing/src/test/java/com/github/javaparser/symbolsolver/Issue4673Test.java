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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

public class Issue4673Test extends AbstractResolutionTest {

    @Test
    void nestedInnerClassCreationWithRecursiveFieldShouldNotStackOverflow() {
        JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));

        CompilationUnit cu = parser.parse("package p;\n"
                + "\n"
                + "class A {\n"
                + "    A a;\n"
                + "    class Inner {\n"
                + "    }\n"
                + "    void f(A a) {\n"
                + "        a.a.a.new Inner();\n"
                + "    }\n"
                + "}\n");

        ObjectCreationExpr objectCreationExpr = cu.findFirst(ObjectCreationExpr.class)
                .orElseThrow(() -> new AssertionError("expected an ObjectCreationExpr"));

        // Resolving the qualified inner-class instantiation "a.a.a.new Inner()" used to
        // recurse without bound and throw a StackOverflowError.
        ResolvedConstructorDeclaration resolved = assertDoesNotThrow(objectCreationExpr::resolve);
        assertEquals("p.A.Inner.Inner", resolved.getQualifiedName());
    }
}
