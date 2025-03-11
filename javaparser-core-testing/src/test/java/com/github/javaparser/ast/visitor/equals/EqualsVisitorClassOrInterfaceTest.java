/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import org.junit.jupiter.api.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

class EqualsVisitorClassOrInterfaceTest extends EqualsVisitorTest
{
    private static final String CLASS = "@anno public sealed class a <T> extends b implements c permits d{" + "void e(){}" + "}";

    @Test
    void equals_sameClass_true()
    {
        parseAndClone(CLASS);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentClass_false()
    {
        parseAndClone(CLASS);
        SimpleName className = getRightClass().getName();
        className.setIdentifier(className.getIdentifier() + ".differentName");
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    ClassOrInterfaceDeclaration getRightClass()
    {
        return nodeRight.getType(0).asClassOrInterfaceDeclaration();
    }

    @Test
    void equals_differentClassAnnotation_false()
    {
        parseAndClone(CLASS);
        getRightClass().getAnnotations().remove(0);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_leftIsClassRightIsInterface_false()
    {
        parseAndClone(CLASS);
        getRightClass().setInterface(true);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExtends_false()
    {
        parseAndClone(CLASS);
        getRightClass().getExtendedTypes(0).remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentImplements_false()
    {
        parseAndClone(CLASS);
        getRightClass().getImplementedTypes(0).remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentPermittedTypes_false()
    {
        parseAndClone(CLASS);
        getRightClass().getPermittedTypes().get(0).remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTypeParameters_false()
    {
        parseAndClone(CLASS);
        getRightClass().getTypeParameters().get(0).remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMembers_false()
    {
        parseAndClone(CLASS);
        getRightClass().getMembers().remove(0);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModifiers_false()
    {
        parseAndClone(CLASS);
        getRightClass().getModifiers().remove(0);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
