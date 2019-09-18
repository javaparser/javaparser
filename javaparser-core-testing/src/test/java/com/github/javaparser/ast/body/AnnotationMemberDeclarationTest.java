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

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

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
}
