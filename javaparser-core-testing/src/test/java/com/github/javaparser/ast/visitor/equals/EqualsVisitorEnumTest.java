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

import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import org.junit.jupiter.api.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

class EqualsVisitorEnumTest extends EqualsVisitorTest
{
    private static final String ENUM = "public @anno enum a implements c{@anno B(1){long f;}; int d;}";

    @Test
    void equals_sameEnum_true()
    {
        parseAndClone(ENUM);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentEntries_false()
    {
        parseAndClone(ENUM);
        EnumDeclaration enumType = getRightEnum();
        enumType.getEntries().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    EnumDeclaration getRightEnum()
    {
        return nodeRight.getType(0).asEnumDeclaration();
    }

    @Test
    void equals_differentImplemented_false()
    {
        parseAndClone(ENUM);
        EnumDeclaration enumType = getRightEnum();
        enumType.getImplementedTypes().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMember_false()
    {
        parseAndClone(ENUM);
        EnumDeclaration enumType = getRightEnum();
        enumType.getMembers().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModifier_false()
    {
        parseAndClone(ENUM);
        EnumDeclaration enumType = getRightEnum();
        enumType.getModifiers().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentName_false()
    {
        parseAndClone(ENUM);
        EnumDeclaration enumType = getRightEnum();
        enumType.setName(enumType.getName()+"differentName");
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAnnotation_false()
    {
        parseAndClone(ENUM);
        EnumDeclaration enumType = getRightEnum();
        enumType.getAnnotations().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentEnumConstantArgument_false()
    {
        parseAndClone(ENUM);
        EnumConstantDeclaration enumConstant = getRightEnum().getEntry(0);
        enumConstant.getArguments().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentEnumConstantBody_false()
    {
        parseAndClone(ENUM);
        EnumConstantDeclaration enumConstant = getRightEnum().getEntry(0);
        enumConstant.getClassBody().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentEnumConstantName_false()
    {
        parseAndClone(ENUM);
        EnumConstantDeclaration enumConstant = getRightEnum().getEntry(0);
        enumConstant.setName(enumConstant.getName()+"differentName");
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentEnumConstantAnnotation_false()
    {
        parseAndClone(ENUM);
        EnumConstantDeclaration enumConstant = getRightEnum().getEntry(0);
        enumConstant.getAnnotations().clear();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
