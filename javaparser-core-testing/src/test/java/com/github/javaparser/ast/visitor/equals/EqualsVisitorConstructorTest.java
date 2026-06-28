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
package com.github.javaparser.ast.visitor.equals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.body.ConstructorDeclaration;
import org.junit.jupiter.api.Test;

public class EqualsVisitorConstructorTest extends EqualsVisitorTest {
    private static final String CONSTRUCTOR = "class X { @anno private <T> X(int a) throws Exception {int i; } }";

    @Test
    void equals_sameConstructor_true() {
        parseAndClone(CONSTRUCTOR);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    ConstructorDeclaration getRightConstructor() {
        return nodeRight.getType(0).getConstructors().get(0);
    }

    @Test
    void equals_differentBody_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getBody().getStatements().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModifier_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentName_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.setName(constructor.getName() + "differentName");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentParameters_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getParameters().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentThrownExceptions_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getThrownExceptions().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTypeParameters_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getTypeParameters().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAnnotations_false() {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentConstructorComment_false() {
        parseAndClone(CONSTRUCTOR);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightConstructor().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
