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

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import org.junit.jupiter.api.Test;

public class EqualsVisitorTypeTest extends EqualsVisitorTest {
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

    @Test
    void classOrInterfaceType_same_true() {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void classOrInterfaceType_differentName_false() {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setName("Set");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void classOrInterfaceType_differentScope_false() {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setScope(null);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void classOrInterfaceType_differentTypeArguments_false() {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setTypeArguments((NodeList<Type>) null);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void classOrInterfaceType_differentAnnotations_false() {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void classOrInterfaceType_differentComment_false() {
        parseAndClone(CLASS_OR_INTERFACE_TYPE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ClassOrInterfaceType type = nodeRight
                .findFirst(ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // PrimitiveType tests

    @Test
    void primitiveType_differentType_false() {
        parseAndClone(PRIMITIVE);
        PrimitiveType type = nodeRight.findFirst(PrimitiveType.class).get();
        type.setType(PrimitiveType.Primitive.DOUBLE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void primitiveType_differentAnnotations_false() {
        parseAndClone(PRIMITIVE);
        PrimitiveType type = nodeRight.findFirst(PrimitiveType.class).get();
        type.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void primitiveType_differentComment_false() {
        parseAndClone(PRIMITIVE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        PrimitiveType type = nodeRight.findFirst(PrimitiveType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ArrayType tests

    @Test
    void arrayType_differentComponentType_false() {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.setComponentType(PrimitiveType.doubleType());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void arrayType_differentOrigin_false() {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.setOrigin(ArrayType.Origin.NAME);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void arrayType_differentAnnotations_false() {
        parseAndClone(ARRAY_TYPE);
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void arrayType_differentComment_false() {
        parseAndClone(ARRAY_TYPE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ArrayType type = nodeRight.findFirst(ArrayType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ArrayCreationLevel tests

    @Test
    void arrayCreationLevel_differentAnnotations_false() {
        parseAndClone(ARRAY_CREATION);
        ArrayCreationLevel level = nodeRight.findFirst(ArrayCreationLevel.class).get();
        level.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void arrayCreationLevel_differentDimension_false() {
        parseAndClone(ARRAY_CREATION);
        ArrayCreationLevel level = nodeRight.findFirst(ArrayCreationLevel.class).get();
        level.setDimension(null);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void arrayCreationLevel_differentComment_false() {
        parseAndClone(ARRAY_CREATION);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ArrayCreationLevel level = nodeRight.findFirst(ArrayCreationLevel.class).get();
        level.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // IntersectionType tests

    @Test
    void intersectionType_same_true() throws Exception {
        parseAndClone(INTERSECTION);
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void intersectionType_differentElements_false() {
        parseAndClone(INTERSECTION);
        IntersectionType type = nodeRight.findFirst(IntersectionType.class).get();
        type.getElements().remove(0);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void intersectionType_differentAnnotations_false() throws Exception {
        parseAndClone(INTERSECTION);
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void intersectionType_differentComment_false() {
        parseAndClone(INTERSECTION);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        IntersectionType type = nodeRight.findFirst(IntersectionType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // UnionType tests

    @Test
    void unionType_same_true() throws Exception {
        parseAndClone(UNION);
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void unionType_differentElements_false() {
        parseAndClone(UNION);
        UnionType type = nodeRight.findFirst(UnionType.class).get();
        type.getElements().remove(0);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void unionType_differentAnnotations_false() throws Exception {
        parseAndClone(UNION);
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void unionType_differentComment_false() {
        parseAndClone(UNION);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        UnionType type = nodeRight.findFirst(UnionType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // VoidType tests

    @Test
    void voidType_differentAnnotations_false() {
        parseAndClone(VOID);
        VoidType type = nodeRight.findFirst(VoidType.class).get();
        type.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void voidType_differentComment_false() {
        parseAndClone(VOID);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        VoidType type = nodeRight.findFirst(VoidType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // WildcardType tests

    @Test
    void wildcardType_differentExtendedType_false() {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.setExtendedType(null);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void wildcardType_differentSuperType_false() {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.setSuperType(new ClassOrInterfaceType(null, "Object"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void wildcardType_differentAnnotations_false() {
        parseAndClone(WILDCARD);
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void wildcardType_differentComment_false() {
        parseAndClone(WILDCARD);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        WildcardType type = nodeRight.findFirst(WildcardType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // UnknownType tests

    @Test
    void unknownType_same_true() throws Exception {
        parseAndClone(UNKNOWN_TYPE);
        UnknownType left = nodeLeft.findFirst(UnknownType.class).get();
        UnknownType right = nodeRight.findFirst(UnknownType.class).get();
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void unknownType_differentAnnotations_false() throws Exception {
        parseAndClone(UNKNOWN_TYPE);
        UnknownType left = nodeLeft.findFirst(UnknownType.class).get();
        UnknownType right = nodeRight.findFirst(UnknownType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void unknownType_differentComment_false() {
        parseAndClone(UNKNOWN_TYPE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        UnknownType type = nodeRight.findFirst(UnknownType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // VarType tests

    @Test
    void varType_same_true() throws Exception {
        parseAndClone(VAR_TYPE);
        VarType left = nodeLeft.findFirst(VarType.class).get();
        VarType right = nodeRight.findFirst(VarType.class).get();
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void varType_differentAnnotations_false() throws Exception {
        parseAndClone(VAR_TYPE);
        VarType left = nodeLeft.findFirst(VarType.class).get();
        VarType right = nodeRight.findFirst(VarType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        boolean result = visitor.visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void varType_differentComment_false() {
        parseAndClone(VAR_TYPE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        VarType type = nodeRight.findFirst(VarType.class).get();
        type.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
