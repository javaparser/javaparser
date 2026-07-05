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
package com.github.javaparser.ast.visitor;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsAnnotationExprTest extends AbstractEqualsVisitorsTest {
    private static final String CODE = "@Marker @Single(1) @Normal(key=2) class X {}";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameAnnotationExprs_true(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_markerDifferentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MarkerAnnotationExpr.class).get().setName("Other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_markerDifferentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MarkerAnnotationExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_singleMemberDifferentMemberValue_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SingleMemberAnnotationExpr.class).get().setMemberValue(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_singleMemberDifferentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SingleMemberAnnotationExpr.class).get().setName("Other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_singleMemberDifferentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SingleMemberAnnotationExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_normalDifferentPairs_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(NormalAnnotationExpr.class).get().getPairs().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_normalDifferentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(NormalAnnotationExpr.class).get().setName("Other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_normalDifferentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(NormalAnnotationExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_memberValuePairDifferentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MemberValuePair.class).get().setName("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_memberValuePairDifferentValue_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MemberValuePair.class).get().setValue(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_memberValuePairDifferentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MemberValuePair.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
