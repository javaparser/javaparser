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

import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import org.junit.jupiter.api.Test;

public class EqualsVisitorAnnotationTest extends EqualsVisitorTest {
    private static final String ANNO = "@anno public @interface anno{@anno public int b() default 3;}";

    @Test
    void equals_sameAnnotation_true() {
        parseAndClone(ANNO);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentMember_false() {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.getMembers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    AnnotationDeclaration getRightAnnotation() {
        return nodeRight.getType(0).asAnnotationDeclaration();
    }

    @Test
    void equals_differentModifier_false() {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentName_false() {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.setName(anno.getName() + "differentName");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAnnotation_false() {
        parseAndClone(ANNO);
        AnnotationDeclaration anno = getRightAnnotation();
        anno.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMemberDefaultValue_false() {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.setDefaultValue(new IntegerLiteralExpr("4"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMemberModifier_false() {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMemberName_false() {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.setName(annoMember.getName() + "differentName");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMemberType_false() {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.setType("long");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMemberAnnotation_false() {
        parseAndClone(ANNO);
        AnnotationMemberDeclaration annoMember =
                getRightAnnotation().getMember(0).asAnnotationMemberDeclaration();
        annoMember.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAnnotationDeclComment_false() {
        parseAndClone(ANNO);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightAnnotation().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAnnotationMemberComment_false() {
        parseAndClone(ANNO);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightAnnotation()
                .getMember(0)
                .asAnnotationMemberDeclaration()
                .setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
