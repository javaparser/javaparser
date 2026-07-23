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

import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsRecordTest extends AbstractEqualsVisitorsTest {
    private static final String RECORD =
            "@anno public record MyRecord<T>(int a) implements java.io.Serializable { public MyRecord { } void helper(){} }";

    // --- RecordDeclaration ---

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameRecord_true(Strategy strategy) {
        parseAndClone(RECORD);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    RecordDeclaration getRightRecord() {
        return nodeRight.findFirst(RecordDeclaration.class).get();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentImplementedTypes_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().getImplementedTypes().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentParameters_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().getParameters().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentReceiverParameter_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord()
                .setReceiverParameter(new com.github.javaparser.ast.body.ReceiverParameter(
                        new com.github.javaparser.ast.type.ClassOrInterfaceType("MyRecord"),
                        new com.github.javaparser.ast.expr.Name("MyRecord")));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentTypeParameters_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().getTypeParameters().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentMembers_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().getMembers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentModifiers_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentName_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().setName("Other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentAnnotations_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentComment(Strategy strategy) {
        parseAndClone(RECORD);
        getRightRecord().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // --- CompactConstructorDeclaration ---

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameCompactConstructor_true(Strategy strategy) {
        parseAndClone(RECORD);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    CompactConstructorDeclaration getRightCompactConstructor() {
        return nodeRight.findFirst(CompactConstructorDeclaration.class).get();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentBody_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor().getBody().getStatements().add(new com.github.javaparser.ast.stmt.ReturnStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentModifiers_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor().getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentName_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor().setName("Other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentThrownExceptions_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor()
                .addThrownException(new com.github.javaparser.ast.type.ClassOrInterfaceType("Exception"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentTypeParameters_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor().getTypeParameters().add(new com.github.javaparser.ast.type.TypeParameter("U"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentAnnotations_false(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor().addMarkerAnnotation("Override");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentComment(Strategy strategy) {
        parseAndClone(RECORD);
        getRightCompactConstructor().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
