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

import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import org.junit.jupiter.api.Test;

public class EqualsVisitorRecordTest extends EqualsVisitorTest {
    private static final String RECORD =
            "@anno public record MyRecord<T>(int a) implements java.io.Serializable { public MyRecord { } void helper(){} }";

    // --- RecordDeclaration ---

    @Test
    void equals_sameRecord_true() {
        parseAndClone(RECORD);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    RecordDeclaration getRightRecord() {
        return nodeRight.findFirst(RecordDeclaration.class).get();
    }

    @Test
    void equals_record_differentImplementedTypes_false() {
        parseAndClone(RECORD);
        getRightRecord().getImplementedTypes().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentParameters_false() {
        parseAndClone(RECORD);
        getRightRecord().getParameters().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentReceiverParameter_false() {
        parseAndClone(RECORD);
        getRightRecord()
                .setReceiverParameter(new com.github.javaparser.ast.body.ReceiverParameter(
                        new com.github.javaparser.ast.type.ClassOrInterfaceType("MyRecord"),
                        new com.github.javaparser.ast.expr.Name("MyRecord")));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentTypeParameters_false() {
        parseAndClone(RECORD);
        getRightRecord().getTypeParameters().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentMembers_false() {
        parseAndClone(RECORD);
        getRightRecord().getMembers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentModifiers_false() {
        parseAndClone(RECORD);
        getRightRecord().getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentName_false() {
        parseAndClone(RECORD);
        getRightRecord().setName("Other");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentAnnotations_false() {
        parseAndClone(RECORD);
        getRightRecord().getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_record_differentComment_false() {
        parseAndClone(RECORD);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightRecord().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // --- CompactConstructorDeclaration ---

    @Test
    void equals_sameCompactConstructor_true() {
        parseAndClone(RECORD);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    CompactConstructorDeclaration getRightCompactConstructor() {
        return nodeRight.findFirst(CompactConstructorDeclaration.class).get();
    }

    @Test
    void equals_compactConstructor_differentBody_false() {
        parseAndClone(RECORD);
        getRightCompactConstructor().getBody().getStatements().add(new com.github.javaparser.ast.stmt.ReturnStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_compactConstructor_differentModifiers_false() {
        parseAndClone(RECORD);
        getRightCompactConstructor().getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_compactConstructor_differentName_false() {
        parseAndClone(RECORD);
        getRightCompactConstructor().setName("Other");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_compactConstructor_differentThrownExceptions_false() {
        parseAndClone(RECORD);
        getRightCompactConstructor()
                .addThrownException(new com.github.javaparser.ast.type.ClassOrInterfaceType("Exception"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_compactConstructor_differentTypeParameters_false() {
        parseAndClone(RECORD);
        getRightCompactConstructor().getTypeParameters().add(new com.github.javaparser.ast.type.TypeParameter("U"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_compactConstructor_differentAnnotations_false() {
        parseAndClone(RECORD);
        getRightCompactConstructor().addMarkerAnnotation("Override");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_compactConstructor_differentComment_false() {
        parseAndClone(RECORD);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightCompactConstructor().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
