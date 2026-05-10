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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

class AnnotationMemberDeclarationTest {

    @Test
    void whenSettingNameTheParentOfNameIsAssigned() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        SimpleName name = new SimpleName("foo");
        decl.setName(name);
        assertTrue(name.getParentNode().isPresent());
        assertSame(decl, name.getParentNode().get());
    }

    @Test
    void removeDefaultValueWhenNoDefaultValueIsPresent() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        SimpleName name = new SimpleName("foo");
        decl.setName(name);

        decl.removeDefaultValue();

        assertFalse(decl.getDefaultValue().isPresent());
    }

    @Test
    void removeDefaultValueWhenDefaultValueIsPresent() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        SimpleName name = new SimpleName("foo");
        decl.setName(name);
        Expression defaultValue = new IntegerLiteralExpr("2");
        decl.setDefaultValue(defaultValue);

        decl.removeDefaultValue();

        assertFalse(defaultValue.getParentNode().isPresent());
    }

    @Test
    void annotationDeclarationShouldSupportRecordChild() {
        CompilationUnit cu = TestParser.parseCompilationUnit(
                ParserConfiguration.LanguageLevel.BLEEDING_EDGE,
                "" + "@interface Foo {\n" + "    record Bar(String s) {}\n" + "}");

        RecordDeclaration bar =
                cu.getAnnotationDeclarationByName("Foo").get().getMember(0).asRecordDeclaration();

        assertEquals(1, bar.getParameters().size());

        Parameter parameter = bar.getParameter(0);
        assertEquals("String", parameter.getTypeAsString());
        assertEquals("s", parameter.getNameAsString());
    }
}
