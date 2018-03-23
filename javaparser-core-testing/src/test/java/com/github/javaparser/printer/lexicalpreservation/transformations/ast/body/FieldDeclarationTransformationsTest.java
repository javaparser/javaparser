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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast.body;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

/**
 * Transforming FieldDeclaration and verifying the LexicalPreservation works as expected.
 */
public class FieldDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected FieldDeclaration consider(String code) {
        considerCode("class A { " + code + " }");
        return cu.getType(0).getMembers().get(0).asFieldDeclaration();
    }

    // JavaDoc

    // Modifiers

    @Test
    public void addingModifiers() {
        FieldDeclaration it = consider("int A;");
        it.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public int A;", it);
    }

    @Test
    public void removingModifiers() {
        FieldDeclaration it = consider("public int A;");
        it.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("int A;", it);
    }

    @Test
    public void replacingModifiers() {
        FieldDeclaration it = consider("int A;");
        it.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected int A;", it);
    }

    @Test
    public void changingTypes() {
        FieldDeclaration it = consider("int a, b;");
        assertTransformedToString("int a, b;", it);
        it.getVariable(0).setType("Xyz");
        assertTransformedToString(" a, b;", it);
        it.getVariable(1).setType("Xyz");
        assertTransformedToString("Xyz a, b;", it);
    }
}
