/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javassistmodel;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclarationTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableSet;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;

class JavassistRecordDeclarationTest extends AbstractTypeDeclarationTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/record_declarations/Box.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isClass());
    }

    @Test
    void testIsInterface() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isInterface());
    }

    @Test
    void testIsEnum() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isEnum());
    }

    @Test
    void testIsRecord() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertTrue(compilationUnit.isRecord());
    }

    @Test
    void testIsTypeVariable() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isTypeParameter());
    }

    @Test
    void testIsType() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertTrue(compilationUnit.isType());
    }

    @Test
    void testAsType() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
            compilationUnit.asInterface();
        });
    }

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
            compilationUnit.asInterface();
        });
    }

    @Test
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
            compilationUnit.asEnum();
        });
    }

    @Test
    void testAsRecord() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(compilationUnit, compilationUnit.asRecord());
    }

    @Test
    void testGetPackageName() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals("box", compilationUnit.getPackageName());
    }

    @Test
    void testGetClassName() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals("Box", compilationUnit.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals("box.Box", compilationUnit.getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetGenericTypeField() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        List<ResolvedFieldDeclaration> declarationList = compilationUnit.getAllFields();
        assertEquals(1, declarationList.size());

        Map<String, ResolvedType> fields = new HashMap<>();
        for (ResolvedFieldDeclaration fieldDeclaration : declarationList) {
            String name = fieldDeclaration.getName();
            ResolvedType type = fieldDeclaration.getType();
            fields.put(name, type);
        }

        assertTrue(fields.containsKey("value"));
    }

    @Test
    void testGetDeclaredMethods() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        Set<ResolvedMethodDeclaration> methodsSet = compilationUnit.getDeclaredMethods();
        assertEquals(5, methodsSet.size());

        Map<String, MethodUsage> methods = new HashMap<>();
        for (ResolvedMethodDeclaration method : methodsSet) {
            methods.put(method.getName(), new MethodUsage(method));
        }

        assertTrue(methods.containsKey("map"));
        assertEquals(1, methods.get("map").getNoParams());
        assertTrue(methods.containsKey("value"));
        assertEquals(0, methods.get("value").getNoParams());
        assertTrue(methods.containsKey("hashCode"));
        assertEquals(0, methods.get("hashCode").getNoParams());
        assertTrue(methods.containsKey("toString"));
        assertEquals(0, methods.get("toString").getNoParams());
        assertTrue(methods.containsKey("equals"));
        assertEquals(1, methods.get("equals").getNoParams());
    }

    ///
    /// Test ancestors
    ///

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetSuperclass() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                "java.lang.Record",
                compilationUnit
                        .getSuperClass()
                        .orElseThrow(() -> new RuntimeException("super class unexpectedly empty"))
                        .getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetAllSuperclasses() {
        JavassistRecordDeclaration cu = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("java.lang.Record", "java.lang.Object"),
                cu.getAllSuperClasses().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetAllAncestorsWithDepthFirstTraversalOrder() {
        JavassistRecordDeclaration cu = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("java.lang.Record", "java.lang.Object", "box.Foo"),
                cu.getAllAncestors().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Test
    void testGetInterfaces() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("box.Foo"),
                compilationUnit.getInterfaces().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    void testGetAllInterfaces() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("box.Foo"),
                compilationUnit.getAllInterfaces().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.empty();
    }

    @Override
    public AbstractTypeDeclaration createValue() {
        return (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
    }

    @Override
    public boolean isFunctionalInterface(AbstractTypeDeclaration typeDeclaration) {
        return false;
    }

    @Override
    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    public void getAllFieldsCantBeNull() {
        assertNotNull(createValue().getAllFields());
    }
}
