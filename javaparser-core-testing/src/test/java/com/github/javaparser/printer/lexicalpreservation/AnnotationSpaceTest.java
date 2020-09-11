/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import java.util.Optional;
import org.junit.jupiter.api.Test;

public class AnnotationSpaceTest {
    /** Tests that inserted annotations on types are followed by a space. */
    @Test
    public void test() {
        CompilationUnit cu =
                StaticJavaParser.parse(
                        "public class Foo {\n" +
                        "    void myMethod(String param);\n" +
                        "}"
                        );
        LexicalPreservingPrinter.setup(cu);
        // Insert the annotation onto the String parameter type.
        Optional<ClassOrInterfaceType> type = cu.findFirst(ClassOrInterfaceType.class);
        type.get().addAnnotation(new MarkerAnnotationExpr("Nullable"));
        String result = LexicalPreservingPrinter.print(cu);
        System.out.println(result);
        // Verify that there's a space between the annotation and the String type.
        assertTrue(result.contains("@Nullable String"));
    }
}
