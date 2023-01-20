/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.ast.type;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

class ClassOrInterfaceTypeTest {

    @Test
    void testSetName() {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType();

        assertNotEquals("A", classOrInterfaceType.getName().toString());
        classOrInterfaceType.setName("A");
        assertEquals("A", classOrInterfaceType.getName().toString());
    }

    @Test
    void testNestedClass() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType();
        classA.setName("A");
        ClassOrInterfaceType classB = new ClassOrInterfaceType(classA, "B");

        assertEquals("A.B", classB.getNameWithScope());
    }

    @Test
    void testWithGeneric() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        ClassOrInterfaceType classB = new ClassOrInterfaceType(classA, new SimpleName("B"), new NodeList<>(classA));

        assertTrue(classB.getTypeArguments().isPresent());
        assertEquals(1, classB.getTypeArguments().get().size());
        assertEquals(classA, classB.getTypeArguments().get().get(0));

        assertEquals("A.B", classB.getNameWithScope());
        assertEquals("A.B<A>", classB.asString());
    }

    @Test
    void testWithAnnotations() {
        AnnotationExpr annotationExpr = StaticJavaParser.parseAnnotation("@Override");
        ClassOrInterfaceType classA = new ClassOrInterfaceType(
                null, new SimpleName("A"), null, new NodeList<>(annotationExpr));

        assertEquals(1, classA.getAnnotations().size());
        assertEquals(annotationExpr, classA.getAnnotation(0));
    }

    @Test
    void testResolveWithoutCompilationUnit() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        Assertions.assertThrows(IllegalStateException.class, classA::resolve);
    }

    @Test
    void testToDescriptorWithoutCompilationUnit() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        Assertions.assertThrows(IllegalStateException.class, classA::toDescriptor);
    }

    @Test
    void testToClassOrInterfaceType() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");

        Optional<ClassOrInterfaceType> newClass = classA.toClassOrInterfaceType();
        assertTrue(newClass.isPresent());
        assertSame(classA, newClass.get());
    }

    @Test
    void testIfClassOrInterfaceTypeIsCalled() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        classA.ifClassOrInterfaceType(classOrInterfaceType -> assertSame(classA, classOrInterfaceType));
    }

    @Test
    void testAsClassOrInterfaceTypeIsTheSame() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");

        assertTrue(classA.isClassOrInterfaceType());
        assertEquals(classA, classA.asClassOrInterfaceType());
    }

    @Test
    void testCloneClass() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        assertEquals(classA, classA.clone());
    }

    @Test
    void testMetaModel() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        assertEquals(JavaParserMetaModel.classOrInterfaceTypeMetaModel, classA.getMetaModel());
    }

    @Test
    void testAcceptVoidVisitor() {
        ClassOrInterfaceType classA = new ClassOrInterfaceType(null, "A");
        classA.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ClassOrInterfaceType classOrInterfaceType, Object object) {
                super.visit(classOrInterfaceType, object);

                assertEquals(classA, classOrInterfaceType);
            }
        }, null);
    }

}
