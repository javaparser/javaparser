/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.*;

class NameTest {

    @Test
    void outerNameExprIsTheRightMostIdentifier() {
        Name name = parseName("a.b.c");
        assertEquals("c", name.getIdentifier());
    }

    @Test
    void parsingAndUnparsingWorks() {
        Name name = parseName("a.b.c");
        assertEquals("a.b.c", name.asString());
    }

    @Test
    void parsingEmptyNameThrowsException() {
        assertThrows(ParseProblemException.class, () -> parseName(""));
    }

    @Test
    void importName() {
        ImportDeclaration importDeclaration = parseImport("import java.util.List;");

        assertEquals("import java.util.List;" + EOL, importDeclaration.toString());
        assertEquals("import java.util.List;" , ConcreteSyntaxModel.genericPrettyPrint(importDeclaration));
    }

    @Test
    void packageName() {
        CompilationUnit cu = parse("package p1.p2;");

        assertEquals("package p1.p2;" + EOL + EOL, cu.toString());
        assertEquals("package p1.p2;" + EOL + EOL, ConcreteSyntaxModel.genericPrettyPrint(cu));
    }

    @Test
    void isInternalNegative() {
        Name name = parseName("a.b.c");
        assertFalse(name.isInternal());
    }

    @Test
    void isInternalPositive() {
        Name name = parseName("a.b.c");
        assertTrue(name
                .getQualifier().get().isInternal());
        assertTrue(name
                .getQualifier().get()
                .getQualifier().get().isInternal());
    }

    @Test
    void isTopLevelNegative() {
        Name name = parseName("a.b.c");
        assertFalse(name
                .getQualifier().get().isTopLevel());
        assertFalse(name
                .getQualifier().get()
                .getQualifier().get().isTopLevel());
    }

    @Test
    void isTopLevelPositive() {
        Name name = parseName("a.b.c");
        assertTrue(name.isTopLevel());
    }

}