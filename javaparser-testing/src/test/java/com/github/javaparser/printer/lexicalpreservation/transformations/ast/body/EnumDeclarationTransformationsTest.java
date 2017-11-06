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
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

/**
 * Transforming EnumDeclaration and verifying the LexicalPreservation works as expected.
 */
public class EnumDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected EnumDeclaration consider(String code) {
        considerCode(code);
        return cu.getType(0).asEnumDeclaration();
    }

    // Name

    @Test
    public void settingName() throws IOException {
        EnumDeclaration cid = consider("enum A { E1, E2 }");
        cid.setName("B");
        assertTransformedToString("enum B { E1, E2 }", cid);
    }

    // implementedTypes

    // Modifiers

    @Test
    public void addingModifiers() throws IOException {
        EnumDeclaration ed = consider("enum A { E1, E2 }");
        ed.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public enum A { E1, E2 }", ed);
    }

    @Test
    public void removingModifiers() throws IOException {
        EnumDeclaration ed = consider("public enum A { E1, E2 }");
        ed.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("enum A { E1, E2 }", ed);
    }

    @Test
    public void replacingModifiers() throws IOException {
        EnumDeclaration ed = consider("public enum A { E1, E2 }");
        ed.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected enum A { E1, E2 }", ed);
    }

    // members

    // Annotations

    // Javadoc

}
