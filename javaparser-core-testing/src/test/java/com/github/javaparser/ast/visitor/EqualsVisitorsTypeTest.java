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

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.type.*;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsTypeTest extends AbstractEqualsVisitorsTest {
    private static final String CLASS_OR_INTERFACE_TYPE = "class X { java.util.@anno List<String> a; }";
    private static final String PRIMITIVE = "class X { @anno int a; }";
    private static final String ARRAY_TYPE = "class X { int @anno [] a; }";
    private static final String ARRAY_CREATION = "class X { Object a = new int @anno [5][3]; }";
    private static final String INTERSECTION = "class X { void m(){ Object o = (Serializable & Comparable) null; } }";
    private static final String UNION = "class X { void m(){ try{}catch(Exception | Error e){} } }";
    private static final String VOID = "class X { void m(){} }";
    private static final String WILDCARD = "class X { List<@anno ? extends Number> a; }";
    private static final String UNKNOWN_TYPE = "class X { Object a = (x) -> x; }";
    private static final String VAR_TYPE = "class X { void m(){ var x = 1; } }";

    // ClassOrInterfaceType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void classOrInterfaceType_same_true(Strategy strategy) {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void classOrInterfaceType_differentName_false(Strategy strategy) {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setName("Set");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void classOrInterfaceType_differentScope_false(Strategy strategy) {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setScope(null);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void classOrInterfaceType_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setTypeArguments((NodeList<Type>) null);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void classOrInterfaceType_differentAnnotations_false(Strategy strategy) {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.getAnnotations().clear();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void classOrInterfaceType_differentComment(Strategy strategy) {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // PrimitiveType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void primitiveType_differentType_false(Strategy strategy) {
        parseAndClone(PRIMITIVE);
        PrimitiveType type = nodeRight.findFirst(PrimitiveType.class).get();
        type.setType(PrimitiveType.Primitive.DOUBLE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void primitiveType_differentAnnotations_false(Strategy strategy) {
        parseAndClone(PRIMITIVE);
        PrimitiveType type = nodeRight.findFirst(PrimitiveType.class).get();
        type.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void primitiveType_differentComment(Strategy strategy) {
        parseAndClone(PRIMITIVE);
        PrimitiveType type = nodeRight.findFirst(PrimitiveType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ArrayType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayType_differentComponentType_false(Strategy strategy) {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.setComponentType(PrimitiveType.doubleType());
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayType_differentOrigin_false(Strategy strategy) {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.setOrigin(ArrayType.Origin.NAME);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayType_differentAnnotations_false(Strategy strategy) {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.getAnnotations().clear();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayType_differentComment(Strategy strategy) {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ArrayCreationLevel tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayCreationLevel_differentAnnotations_false(Strategy strategy) {
        parseAndClone(ARRAY_CREATION);
        ArrayCreationLevel level = nodeRight.findFirst(ArrayCreationLevel.class).get();
        level.getAnnotations().clear();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayCreationLevel_differentDimension_false(Strategy strategy) {
        parseAndClone(ARRAY_CREATION);
        ArrayCreationLevel level = nodeRight.findFirst(ArrayCreationLevel.class).get();
        level.setDimension(null);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void arrayCreationLevel_differentComment(Strategy strategy) {
        parseAndClone(ARRAY_CREATION);
        ArrayCreationLevel level = nodeRight.findFirst(ArrayCreationLevel.class).get();
        level.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // IntersectionType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void intersectionType_same_true(Strategy strategy) {
        parseAndClone(INTERSECTION);
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        boolean result = strategy.areEqual(left, right);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void intersectionType_differentElements_false(Strategy strategy) {
        parseAndClone(INTERSECTION);
        IntersectionType type = nodeRight.findFirst(IntersectionType.class).get();
        type.getElements().remove(0);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void intersectionType_differentAnnotations_false(Strategy strategy) throws Exception {
        parseAndClone(INTERSECTION);
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = strategy.areEqual(left, right);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void intersectionType_differentComment(Strategy strategy) {
        parseAndClone(INTERSECTION);
        IntersectionType type = nodeRight.findFirst(IntersectionType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // UnionType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unionType_same_true(Strategy strategy) {
        parseAndClone(UNION);
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        boolean result = strategy.areEqual(left, right);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unionType_differentElements_false(Strategy strategy) {
        parseAndClone(UNION);
        UnionType type = nodeRight.findFirst(UnionType.class).get();
        type.getElements().remove(0);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unionType_differentAnnotations_false(Strategy strategy) throws Exception {
        parseAndClone(UNION);
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = strategy.areEqual(left, right);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unionType_differentComment(Strategy strategy) {
        parseAndClone(UNION);
        UnionType type = nodeRight.findFirst(UnionType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // VoidType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void voidType_differentAnnotations_false(Strategy strategy) {
        parseAndClone(VOID);
        VoidType type = nodeRight.findFirst(VoidType.class).get();
        type.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void voidType_differentComment(Strategy strategy) {
        parseAndClone(VOID);
        VoidType type = nodeRight.findFirst(VoidType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // WildcardType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void wildcardType_differentExtendedType_false(Strategy strategy) {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.setExtendedType(null);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void wildcardType_differentSuperType_false(Strategy strategy) {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.setSuperType(new ClassOrInterfaceType(null, "Object"));
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void wildcardType_differentAnnotations_false(Strategy strategy) {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.getAnnotations().clear();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void wildcardType_differentComment(Strategy strategy) {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // UnknownType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unknownType_same_true(Strategy strategy) throws Exception {
        parseAndClone(UNKNOWN_TYPE);
        UnknownType left = nodeLeft.findFirst(UnknownType.class).get();
        UnknownType right = nodeRight.findFirst(UnknownType.class).get();
        boolean result = strategy.areEqual(left, right);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unknownType_differentAnnotations_false(Strategy strategy) throws Exception {
        parseAndClone(UNKNOWN_TYPE);
        UnknownType left = nodeLeft.findFirst(UnknownType.class).get();
        UnknownType right = nodeRight.findFirst(UnknownType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = strategy.areEqual(left, right);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void unknownType_differentComment(Strategy strategy) {
        parseAndClone(UNKNOWN_TYPE);
        UnknownType type = nodeRight.findFirst(UnknownType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // VarType tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void varType_same_true(Strategy strategy) throws Exception {
        parseAndClone(VAR_TYPE);
        VarType left = nodeLeft.findFirst(VarType.class).get();
        VarType right = nodeRight.findFirst(VarType.class).get();
        boolean result = strategy.areEqual(left, right);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void varType_differentAnnotations_false(Strategy strategy) throws Exception {
        parseAndClone(VAR_TYPE);
        VarType left = nodeLeft.findFirst(VarType.class).get();
        VarType right = nodeRight.findFirst(VarType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = strategy.areEqual(left, right);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void varType_differentComment(Strategy strategy) {
        parseAndClone(VAR_TYPE);
        VarType type = nodeRight.findFirst(VarType.class).get();
        type.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
