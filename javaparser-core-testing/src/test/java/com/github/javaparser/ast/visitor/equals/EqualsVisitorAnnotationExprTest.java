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

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import org.junit.jupiter.api.Test;

public class EqualsVisitorAnnotationExprTest extends EqualsVisitorTest {
    private static final String CODE = "@Marker @Single(1) @Normal(key=2) class X {}";

    @Test
    void equals_sameAnnotationExprs_true() {
        parseAndClone(CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_markerDifferentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MarkerAnnotationExpr.class).get().setName("Other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_markerDifferentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(MarkerAnnotationExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_singleMemberDifferentMemberValue_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(SingleMemberAnnotationExpr.class).get().setMemberValue(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_singleMemberDifferentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(SingleMemberAnnotationExpr.class).get().setName("Other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_singleMemberDifferentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(SingleMemberAnnotationExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_normalDifferentPairs_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(NormalAnnotationExpr.class).get().getPairs().clear();
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_normalDifferentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(NormalAnnotationExpr.class).get().setName("Other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_normalDifferentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(NormalAnnotationExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_memberValuePairDifferentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MemberValuePair.class).get().setName("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_memberValuePairDifferentValue_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MemberValuePair.class).get().setValue(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_memberValuePairDifferentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(MemberValuePair.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }
}
