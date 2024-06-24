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

package com.github.javaparser.symbolsolver.reflectionmodel;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableSet;
import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;

@EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
class ReflectionRecordDeclarationTest extends AbstractSymbolResolutionTest {
    private ClassLoader classLoader = new ClassLoader() {
        public Class<?> findClass(String name) {
            String strippedName = name.substring(4);
            byte[] b = loadClassData(strippedName);
            return defineClass(name, b, 0, b.length);
        }

        private byte[] loadClassData(String name) {
            Path filePath = adaptPath(String.format("src/test/resources/record_declarations/%s.class", name));
            try {
                return Files.readAllBytes(filePath);
            } catch (IOException e) {
                return null;
            }
        }
    };
    private TypeSolver typeSolver =
            new CombinedTypeSolver(new ClassLoaderTypeSolver(classLoader), new ReflectionTypeSolver());

    /**
     * The test classes were compiled with Java 17, so attempting to load them with any lower version will crash
     */
    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testIsClass() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isClass());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testIsInterface() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isInterface());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testIsEnum() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isEnum());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testIsRecord() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertTrue(compilationUnit.isRecord());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testIsTypeVariable() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertFalse(compilationUnit.isTypeParameter());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testIsType() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertTrue(compilationUnit.isType());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testAsType() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
            compilationUnit.asInterface();
        });
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
            compilationUnit.asInterface();
        });
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
            compilationUnit.asEnum();
        });
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testAsRecord() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(compilationUnit, compilationUnit.asRecord());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetPackageName() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals("box", compilationUnit.getPackageName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetClassName() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals("Box", compilationUnit.getClassName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetQualifiedName() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals("box.Box", compilationUnit.getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetGenericTypeField() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
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
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetDeclaredMethods() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
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
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetSuperclass() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                "java.lang.Record",
                compilationUnit
                        .getSuperClass()
                        .orElseThrow(() -> new RuntimeException("super class unexpectedly empty"))
                        .getQualifiedName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetAllSuperclasses() {
        ReflectionRecordDeclaration cu = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("java.lang.Record", "java.lang.Object"),
                cu.getAllSuperClasses().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetAllAncestorsWithDepthFirstTraversalOrder() {
        ReflectionRecordDeclaration cu = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("java.lang.Record", "java.lang.Object", "box.Foo"),
                cu.getAllAncestors().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetInterfaces() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("box.Foo"),
                compilationUnit.getInterfaces().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetAllInterfaces() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");
        assertEquals(
                ImmutableSet.of("box.Foo"),
                compilationUnit.getAllInterfaces().stream()
                        .map(ResolvedReferenceType::getQualifiedName)
                        .collect(Collectors.toSet()));
    }
}
