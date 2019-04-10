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

import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Transforming InitializerDeclaration and verifying the LexicalPreservation works as expected.
 */
class InitializerDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected InitializerDeclaration consider(String code) {
        considerCode("class A { " + code + " }");
        return cu.getType(0).getMembers().get(0).asInitializerDeclaration();
    }

    // JavaDoc

    // Body

    // IsStatic

    @Test
    void instanceToStatic() {
        InitializerDeclaration it = consider("{ /*some comment*/ }");
        it.setStatic(true);
        assertTransformedToString("static { /*some comment*/ }", it);
    }

    @Test
    void staticToInstance() {
        InitializerDeclaration it = consider("static { /*some comment*/ }");
        it.setStatic(false);
        assertTransformedToString("{ /*some comment*/ }", it);
    }

    // Annotations
}
