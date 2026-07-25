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

package com.github.javaparser.ast.visitor;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

class NoCommentEqualsVisitorTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    @Test
    void testEquals() {
        CompilationUnit p1 = parser.parse("class X { }");
        CompilationUnit p2 = parser.parse("class X { }");
        assertTrue(NoCommentEqualsVisitor.equals(p1, p2));
    }

    @Test
    void testEqualsWithDifferentComments() {
        CompilationUnit p1 = parser.parse("/* a */ class X { /** b */} //c");
        CompilationUnit p2 = parser.parse("/* b */ class X { }  //c");
        assertTrue(NoCommentEqualsVisitor.equals(p1, p2));
    }

    @Test
    void testNotEquals() {
        CompilationUnit p1 = parser.parse("class X { }");
        CompilationUnit p2 = parser.parse("class Y { }");
        assertFalse(NoCommentEqualsVisitor.equals(p1, p2));
    }
}
