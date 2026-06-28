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

import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.TypeParameter;
import org.junit.jupiter.api.Test;

public class EqualsVisitorTypeParameterTest extends EqualsVisitorTest {
    private static final String TYPE_PARAMETER = " public class a <@Foo T extends Number> {}";

    @Test
    void equals_sameTypeParameter_true() {
        parseAndClone(TYPE_PARAMETER);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentTypeParameter_false() {
        parseAndClone(TYPE_PARAMETER);
        SimpleName typeParameterName = getRightTypeParameter().getName();
        typeParameterName.setIdentifier(typeParameterName.getIdentifier() + "differentName");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    TypeParameter getRightTypeParameter() {
        return nodeRight.getType(0).asClassOrInterfaceDeclaration().getTypeParameter(0);
    }

    @Test
    void equals_differentAnnotation_false() {
        parseAndClone(TYPE_PARAMETER);
        TypeParameter typeParameter = getRightTypeParameter();
        typeParameter.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentBound_false() {
        parseAndClone(TYPE_PARAMETER);
        TypeParameter typeParameter = getRightTypeParameter();
        typeParameter.getTypeBound().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTypeParameterComment_false() {
        parseAndClone(TYPE_PARAMETER);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightTypeParameter().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
