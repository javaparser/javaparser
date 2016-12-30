/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

import static org.junit.Assert.assertEquals;

/**
 * Transforming AnnotationMemberDeclaration and verifying the LexicalPreservation works as expected.
 */
public class AnnotationMemberDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected void assertTransformedToString(String expectedPartialCode, Node node) throws IOException {
        String actualCode = lpp.print(node);
        assertEquals(expectedPartialCode, actualCode);
    }

    // Name

    private AnnotationMemberDeclaration consider(String code) {
        considerCode("@interface AD { " + code + " }");
        return (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("AD").get().getMember(0);
    }

    @Test
    public void changingName() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setName("bar");
        assertTransformedToString("int bar();", md);
    }

    // Type

    // Modifiers

    // Default value

    // Annotations

    // Javadoc

}
