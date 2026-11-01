/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
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

package com.github.javaparser.ast.body;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_16;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

class EnumDeclarationTest {

    // Local enums are only permitted starting with Java 16 (JEP 395).
    private final JavaParserAdapter parser =
            StaticJavaParser.newParserAdapter(new ParserConfiguration().setLanguageLevel(JAVA_16));

    @Test
    void topEnum() {
        CompilationUnit cu = parser.parse("enum E{A}");
        EnumDeclaration e = cu.getEnumByName("E").get();

        assertFalse(e.isNestedType());
        assertFalse(e.isLocalEnumDeclaration());
    }

    @Test
    void nestedEnum() {
        CompilationUnit cu = parser.parse("class X{enum E{A}}");
        EnumDeclaration e = cu.getClassByName("X").get().getMembers().get(0).asEnumDeclaration();

        assertTrue(e.isNestedType());
        assertFalse(e.isLocalEnumDeclaration());
    }

    @Test
    void localEnum() {
        CompilationUnit cu = parser.parse("class X{ void x() {enum E{A}} }");
        EnumDeclaration e = cu.findFirst(EnumDeclaration.class).get();

        assertFalse(e.isNestedType());
        assertTrue(e.isLocalEnumDeclaration());
    }
}
