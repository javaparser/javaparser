/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
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

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsAnnotationTest extends AbstractEqualsVisitorsTest {
    private static final String ANNO = "@anno public @interface anno{@anno public int b() default 3;}";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameAnnotation_true(Strategy strategy) {
        parseAndClone(ANNO);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMember_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.getMembers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    AnnotationDeclaration getRightAnnotation() {
        return nodeRight.getType(0).asAnnotationDeclaration();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModifier_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentName_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.setName(anno.getName() + "differentName");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotation_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMemberDefaultValue_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.setDefaultValue(new IntegerLiteralExpr("4"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMemberModifier_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMemberName_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.setName(annoMember.getName() + "differentName");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMemberType_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.setType("long");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMemberAnnotation_false(Strategy strategy) {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotationDeclComment(Strategy strategy) {
        parseAndClone(ANNO);
        getRightAnnotation().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotationMemberComment(Strategy strategy) {
        parseAndClone(ANNO);
        getRightAnnotation()
                .getMember(0)
                .asAnnotationMemberDeclaration()
                .setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
