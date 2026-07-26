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

package com.github.javaparser.ast.expr;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verifyNoInteractions;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.Test;

class NameTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    @Test
    void outerNameExprIsTheRightMostIdentifier() {
        Name name = parser.parseName("a.b.c");
        assertEquals("c", name.getIdentifier());
    }

    @Test
    void parsingAndUnparsingWorks() {
        Name name = parser.parseName("a.b.c");
        assertEquals("a.b.c", name.asString());
    }

    @Test
    void parsingEmptyNameThrowsException() {
        assertThrows(ParseProblemException.class, () -> parser.parseName(""));
    }

    @Test
    void importName() {
        ImportDeclaration importDeclaration = parser.parseImport("import java.util.List;");

        assertEquals("import java.util.List;" + LineSeparator.SYSTEM, importDeclaration.toString());
        assertEquals("import java.util.List;", ConcreteSyntaxModel.genericPrettyPrint(importDeclaration));
    }

    @Test
    void packageName() {
        CompilationUnit cu = parser.parse("package p1.p2;");

        assertEquals("package p1.p2;" + LineSeparator.SYSTEM + LineSeparator.SYSTEM, cu.toString());
        assertEquals(
                "package p1.p2;" + LineSeparator.SYSTEM + LineSeparator.SYSTEM,
                ConcreteSyntaxModel.genericPrettyPrint(cu));
    }

    @Test
    void isInternalNegative() {
        Name name = parser.parseName("a.b.c");
        assertFalse(name.isInternal());
    }

    @Test
    void isInternalPositive() {
        Name name = parser.parseName("a.b.c");
        assertTrue(name.getQualifier().get().isInternal());
        assertTrue(name.getQualifier().get().getQualifier().get().isInternal());
    }

    @Test
    void isTopLevelNegative() {
        Name name = parser.parseName("a.b.c");
        assertFalse(name.getQualifier().get().isTopLevel());
        assertFalse(name.getQualifier().get().getQualifier().get().isTopLevel());
    }

    @Test
    void isTopLevelPositive() {
        Name name = parser.parseName("a.b.c");
        assertTrue(name.isTopLevel());
    }

    @Test
    void issue4791Test() {
        String a = new String("c");
        String b = new String("c");
        Name expression = new Name(a);

        AstObserver observer = mock(AstObserver.class);
        expression.register(observer);

        expression.setIdentifier(b);

        verifyNoInteractions(observer);
    }
}
