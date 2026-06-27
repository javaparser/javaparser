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
package com.github.javaparser.ast.visitor.nocommentequals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.NoCommentEqualsVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.equals.EqualsVisitorTest;
import org.junit.jupiter.api.Test;

public class NoCommentEqualsVisitorTypeTest extends EqualsVisitorTest {

    @Override
    protected boolean equalsNodes(Node n, Node n2) {
        return NoCommentEqualsVisitor.equals(n, n2);
    }

    private NoCommentEqualsVisitor visitor() throws Exception {
        java.lang.reflect.Field f = NoCommentEqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        return (NoCommentEqualsVisitor) f.get(null);
    }

    // VarType

    @Test
    void visit_varType_same_true() throws Exception {
        parseAndClone("class X { void m(){ var x = 1; } }");
        VarType left = nodeLeft.findFirst(VarType.class).get();
        VarType right = nodeRight.findFirst(VarType.class).get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_varType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { void m(){ var x = 1; } }");
        VarType left = nodeLeft.findFirst(VarType.class).get();
        VarType right = nodeRight.findFirst(VarType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // IntersectionType

    @Test
    void visit_intersectionType_same_true() throws Exception {
        parseAndClone("class X { void m(){ Object o = (Serializable & Comparable) null; } }");
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_intersectionType_differentElements_false() throws Exception {
        parseAndClone("class X { void m(){ Object o = (Serializable & Comparable) null; } }");
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        right.getElements().remove(0);
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_intersectionType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { void m(){ Object o = (Serializable & Comparable) null; } }");
        IntersectionType left = nodeLeft.findFirst(IntersectionType.class).get();
        IntersectionType right = nodeRight.findFirst(IntersectionType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // UnionType

    @Test
    void visit_unionType_same_true() throws Exception {
        parseAndClone("class X { void m(){ try{}catch(Exception | Error e){} } }");
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_unionType_differentElements_false() throws Exception {
        parseAndClone("class X { void m(){ try{}catch(Exception | Error e){} } }");
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        right.getElements().remove(0);
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_unionType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { void m(){ try{}catch(Exception | Error e){} } }");
        UnionType left = nodeLeft.findFirst(UnionType.class).get();
        UnionType right = nodeRight.findFirst(UnionType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // UnknownType

    @Test
    void visit_unknownType_same_true() throws Exception {
        parseAndClone("class X { Object a = (x) -> x; }");
        UnknownType left = nodeLeft.findFirst(UnknownType.class).get();
        UnknownType right = nodeRight.findFirst(UnknownType.class).get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_unknownType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { Object a = (x) -> x; }");
        UnknownType left = nodeLeft.findFirst(UnknownType.class).get();
        UnknownType right = nodeRight.findFirst(UnknownType.class).get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // NodeList

    @SuppressWarnings("unchecked")
    @Test
    void visit_nodeList_same_true() throws Exception {
        parseAndClone("class X { void a(){} void b(){} }");
        NodeList<?> left = nodeLeft.getType(0).asClassOrInterfaceDeclaration().getMembers();
        NodeList<?> right = nodeRight.getType(0).asClassOrInterfaceDeclaration().getMembers();
        boolean result = (Boolean) ((NodeList) left).accept(visitor(), right);
        assertThat(result, is(true));
    }

    @SuppressWarnings("unchecked")
    @Test
    void visit_nodeList_different_false() throws Exception {
        parseAndClone("class X { void a(){} void b(){} }");
        NodeList<?> left = nodeLeft.getType(0).asClassOrInterfaceDeclaration().getMembers();
        NodeList<?> right = nodeRight.getType(0).asClassOrInterfaceDeclaration().getMembers();
        ((NodeList) right).remove(0);
        boolean result = (Boolean) ((NodeList) left).accept(visitor(), right);
        assertThat(result, is(false));
    }

    // ClassOrInterfaceType

    @Test
    void visit_classOrInterfaceType_same_true() throws Exception {
        parseAndClone("class X { java.util.List<String> a; }");
        com.github.javaparser.ast.type.ClassOrInterfaceType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        com.github.javaparser.ast.type.ClassOrInterfaceType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_classOrInterfaceType_differentScope_false() throws Exception {
        parseAndClone("class X { java.util.List<String> a; }");
        com.github.javaparser.ast.type.ClassOrInterfaceType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        com.github.javaparser.ast.type.ClassOrInterfaceType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        right.setScope(null);
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_classOrInterfaceType_differentTypeArguments_false() throws Exception {
        parseAndClone("class X { java.util.List<String> a; }");
        com.github.javaparser.ast.type.ClassOrInterfaceType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        com.github.javaparser.ast.type.ClassOrInterfaceType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        right.getTypeArguments().get().clear();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_classOrInterfaceType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { java.util.List<String> a; }");
        com.github.javaparser.ast.type.ClassOrInterfaceType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        com.github.javaparser.ast.type.ClassOrInterfaceType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ClassOrInterfaceType.class)
                .get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // PrimitiveType

    @Test
    void visit_primitiveType_same_true() throws Exception {
        parseAndClone("class X { @anno int a; }");
        com.github.javaparser.ast.type.PrimitiveType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.PrimitiveType.class)
                .get();
        com.github.javaparser.ast.type.PrimitiveType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.PrimitiveType.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_primitiveType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { int a; }");
        com.github.javaparser.ast.type.PrimitiveType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.PrimitiveType.class)
                .get();
        com.github.javaparser.ast.type.PrimitiveType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.PrimitiveType.class)
                .get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // ArrayType

    @Test
    void visit_arrayType_same_true() throws Exception {
        parseAndClone("class X { int[] a; }");
        com.github.javaparser.ast.type.ArrayType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ArrayType.class)
                .get();
        com.github.javaparser.ast.type.ArrayType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ArrayType.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_arrayType_differentComponent_false() throws Exception {
        parseAndClone("class X { int[] a; }");
        com.github.javaparser.ast.type.ArrayType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ArrayType.class)
                .get();
        com.github.javaparser.ast.type.ArrayType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ArrayType.class)
                .get();
        right.setComponentType(new com.github.javaparser.ast.type.PrimitiveType(
                com.github.javaparser.ast.type.PrimitiveType.Primitive.LONG));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_arrayType_differentOrigin_false() throws Exception {
        parseAndClone("class X { int[] a; }");
        com.github.javaparser.ast.type.ArrayType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ArrayType.class)
                .get();
        com.github.javaparser.ast.type.ArrayType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ArrayType.class)
                .get();
        right.setOrigin(com.github.javaparser.ast.type.ArrayType.Origin.NAME);
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_arrayType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { int[] a; }");
        com.github.javaparser.ast.type.ArrayType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.ArrayType.class)
                .get();
        com.github.javaparser.ast.type.ArrayType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.ArrayType.class)
                .get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // ArrayCreationLevel

    @Test
    void visit_arrayCreationLevel_same_true() throws Exception {
        parseAndClone("class X { Object a = new int[5]; }");
        com.github.javaparser.ast.ArrayCreationLevel left = nodeLeft.findFirst(
                        com.github.javaparser.ast.ArrayCreationLevel.class)
                .get();
        com.github.javaparser.ast.ArrayCreationLevel right = nodeRight
                .findFirst(com.github.javaparser.ast.ArrayCreationLevel.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_arrayCreationLevel_differentDimension_false() throws Exception {
        parseAndClone("class X { Object a = new int[5]; }");
        com.github.javaparser.ast.ArrayCreationLevel left = nodeLeft.findFirst(
                        com.github.javaparser.ast.ArrayCreationLevel.class)
                .get();
        com.github.javaparser.ast.ArrayCreationLevel right = nodeRight
                .findFirst(com.github.javaparser.ast.ArrayCreationLevel.class)
                .get();
        right.setDimension(new com.github.javaparser.ast.expr.IntegerLiteralExpr("9"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_arrayCreationLevel_differentAnnotations_false() throws Exception {
        parseAndClone("class X { Object a = new int[5]; }");
        com.github.javaparser.ast.ArrayCreationLevel left = nodeLeft.findFirst(
                        com.github.javaparser.ast.ArrayCreationLevel.class)
                .get();
        com.github.javaparser.ast.ArrayCreationLevel right = nodeRight
                .findFirst(com.github.javaparser.ast.ArrayCreationLevel.class)
                .get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // VoidType

    @Test
    void visit_voidType_same_true() throws Exception {
        parseAndClone("class X { void m(){} }");
        com.github.javaparser.ast.type.VoidType left = nodeLeft.findFirst(com.github.javaparser.ast.type.VoidType.class)
                .get();
        com.github.javaparser.ast.type.VoidType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.VoidType.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_voidType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { void m(){} }");
        com.github.javaparser.ast.type.VoidType left = nodeLeft.findFirst(com.github.javaparser.ast.type.VoidType.class)
                .get();
        com.github.javaparser.ast.type.VoidType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.VoidType.class)
                .get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // WildcardType

    @Test
    void visit_wildcardType_same_true() throws Exception {
        parseAndClone("class X { java.util.List<@anno ? super Number> a; }");
        com.github.javaparser.ast.type.WildcardType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.WildcardType.class)
                .get();
        com.github.javaparser.ast.type.WildcardType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.WildcardType.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_wildcardType_differentExtended_false() throws Exception {
        parseAndClone("class X { java.util.List<? extends Number> a; }");
        com.github.javaparser.ast.type.WildcardType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.WildcardType.class)
                .get();
        com.github.javaparser.ast.type.WildcardType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.WildcardType.class)
                .get();
        right.removeExtendedType();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_wildcardType_differentSuper_false() throws Exception {
        parseAndClone("class X { java.util.List<? super Number> a; }");
        com.github.javaparser.ast.type.WildcardType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.WildcardType.class)
                .get();
        com.github.javaparser.ast.type.WildcardType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.WildcardType.class)
                .get();
        right.removeSuperType();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_wildcardType_differentAnnotations_false() throws Exception {
        parseAndClone("class X { java.util.List<? super Number> a; }");
        com.github.javaparser.ast.type.WildcardType left = nodeLeft.findFirst(
                        com.github.javaparser.ast.type.WildcardType.class)
                .get();
        com.github.javaparser.ast.type.WildcardType right = nodeRight
                .findFirst(com.github.javaparser.ast.type.WildcardType.class)
                .get();
        left.getAnnotations().add(new MarkerAnnotationExpr("Extra"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }
}
