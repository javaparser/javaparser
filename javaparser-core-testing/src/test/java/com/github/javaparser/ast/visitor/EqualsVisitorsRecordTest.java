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

import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
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
        assertNotEqualAfterMutation(
                RECORD, this::getRightRecord, n -> n.getImplementedTypes().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightRecord, n -> n.getParameters().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentReceiverParameter_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD,
                this::getRightRecord,
                n -> n.setReceiverParameter(new com.github.javaparser.ast.body.ReceiverParameter(
                        new com.github.javaparser.ast.type.ClassOrInterfaceType("MyRecord"),
                        new com.github.javaparser.ast.expr.Name("MyRecord"))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentTypeParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightRecord, n -> n.getTypeParameters().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentMembers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightRecord, n -> n.getMembers().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentModifiers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightRecord, n -> n.getModifiers().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(RECORD, this::getRightRecord, n -> n.setName("Other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentAnnotations_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightRecord, n -> n.getAnnotations().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_record_differentComment(Strategy strategy) {
        assertCommentChangeHandled(RECORD, () -> getRightRecord(), strategy);
    }

    // --- CompactConstructorDeclaration ---

    CompactConstructorDeclaration getRightCompactConstructor() {
        return nodeRight.findFirst(CompactConstructorDeclaration.class).get();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD,
                this::getRightCompactConstructor,
                n -> n.getBody().getStatements().add(new com.github.javaparser.ast.stmt.ReturnStmt()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentModifiers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightCompactConstructor, n -> n.getModifiers().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(RECORD, this::getRightCompactConstructor, n -> n.setName("Other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentThrownExceptions_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD,
                this::getRightCompactConstructor,
                n -> n.addThrownException(new com.github.javaparser.ast.type.ClassOrInterfaceType("Exception")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentTypeParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD,
                this::getRightCompactConstructor,
                n -> n.getTypeParameters().add(new com.github.javaparser.ast.type.TypeParameter("U")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentAnnotations_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                RECORD, this::getRightCompactConstructor, n -> n.addMarkerAnnotation("Override"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_compactConstructor_differentComment(Strategy strategy) {
        assertCommentChangeHandled(RECORD, () -> getRightCompactConstructor(), strategy);
    }
}
