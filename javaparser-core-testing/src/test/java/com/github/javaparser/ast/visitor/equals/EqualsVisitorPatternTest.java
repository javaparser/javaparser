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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.MatchAllPatternExpr;
import com.github.javaparser.ast.expr.RecordPatternExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorPatternTest extends EqualsVisitorTest {

    private static final String TYPE_PATTERN_CODE = "class X { void m(Object o){ if(o instanceof final String s){} } }";
    private static final String RECORD_PATTERN_CODE =
            "class X { record Point(int x, int y){} void m(Object o){ if(o instanceof Point(int x, int y)){} } }";
    private static final String MATCH_ALL_CODE =
            "class X { record Box(Object v){} void m(Object o){ switch(o){ case Box(_) -> {} default -> {} } } }";

    // TypePatternExpr tests

    @Test
    void equals_typePattern_same_true() {
        parseAndClone(TYPE_PATTERN_CODE);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(true));
    }

    @Test
    void equals_typePattern_differentModifiers_false() {
        parseAndClone(TYPE_PATTERN_CODE);
        nodeRight.findFirst(TypePatternExpr.class).get().setModifiers(new NodeList<>());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_typePattern_differentName_false() {
        parseAndClone(TYPE_PATTERN_CODE);
        nodeRight.findFirst(TypePatternExpr.class).get().setName(new SimpleName("other"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_typePattern_differentType_false() {
        parseAndClone(TYPE_PATTERN_CODE);
        nodeRight.findFirst(TypePatternExpr.class).get().setType(new ClassOrInterfaceType("Integer"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_typePattern_differentComment_false() {
        parseAndClone(TYPE_PATTERN_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(TypePatternExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // RecordPatternExpr tests

    @Test
    void equals_recordPattern_same_true() {
        parseAndClone(RECORD_PATTERN_CODE);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(true));
    }

    @Test
    void equals_recordPattern_differentModifiers_false() {
        parseAndClone(RECORD_PATTERN_CODE);
        nodeRight.findFirst(RecordPatternExpr.class).get().setModifiers(new NodeList<>(Modifier.finalModifier()));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_recordPattern_differentPatternList_false() {
        parseAndClone(RECORD_PATTERN_CODE);
        nodeRight.findFirst(RecordPatternExpr.class).get().setPatternList(new NodeList<>());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_recordPattern_differentType_false() {
        parseAndClone(RECORD_PATTERN_CODE);
        nodeRight.findFirst(RecordPatternExpr.class).get().setType(new ClassOrInterfaceType("Other"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_recordPattern_differentComment_false() {
        parseAndClone(RECORD_PATTERN_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(RecordPatternExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // MatchAllPatternExpr tests

    @Test
    void equals_matchAllPattern_same_true() {
        parseAndClone(MATCH_ALL_CODE);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(true));
    }

    @Test
    void equals_matchAllPattern_differentModifiers_false() {
        parseAndClone(MATCH_ALL_CODE);
        nodeRight.findFirst(MatchAllPatternExpr.class).get().setModifiers(new NodeList<>(Modifier.finalModifier()));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_matchAllPattern_differentComment_false() {
        parseAndClone(MATCH_ALL_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(MatchAllPatternExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }
}
