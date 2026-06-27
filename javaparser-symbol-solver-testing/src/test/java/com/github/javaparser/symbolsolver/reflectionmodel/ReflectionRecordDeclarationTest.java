/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
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
        public Class<?> findClass(String name) throws ClassNotFoundException {
            if (name.startsWith("java.lang")) {
                throw new ClassNotFoundException("Cannot define classes in java.lang");
            }
            int beginIndex = Math.max(0, name.lastIndexOf('.') + 1);
            String strippedName = name.substring(beginIndex);
            byte[] b = loadClassData(strippedName);
            return defineClass(name, b, 0, b.length);
        }

        private byte[] loadClassData(String name) throws ClassNotFoundException {
            try {
                Path filePath = adaptPath(String.format("src/test/resources/record_declarations/box/%s.class", name));
                return Files.readAllBytes(filePath);
            } catch (Exception e) {
                throw new ClassNotFoundException(e.getMessage());
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
        assertInstanceOf(
                ResolvedRecordDeclaration.class,
                methods.get("map").getDeclaration().declaringType());
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

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetImplicitConstructor() {
        ReflectionRecordDeclaration compilationUnit = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");

        assertEquals(1, compilationUnit.getConstructors().size());

        ResolvedConstructorDeclaration constructor =
                compilationUnit.getConstructors().get(0);

        assertEquals("Box", constructor.getName());
        assertEquals("box.Box.Box", constructor.getQualifiedName());
        assertEquals(1, constructor.getNumberOfParams());
        assertEquals("box", constructor.getPackageName());
        assertEquals("Box", constructor.getClassName());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testGetExplicitConstructors() {
        ReflectionRecordDeclaration compilationUnit =
                (ReflectionRecordDeclaration) typeSolver.solveType("box.BoxWithAllConstructors");

        assertEquals(2, compilationUnit.getConstructors().size());

        ResolvedConstructorDeclaration stringConstructor =
                compilationUnit.getConstructors().get(0);

        assertEquals("BoxWithAllConstructors", stringConstructor.getName());
        assertEquals("box.BoxWithAllConstructors.BoxWithAllConstructors", stringConstructor.getQualifiedName());
        assertEquals(1, stringConstructor.getNumberOfParams());
        assertEquals("box", stringConstructor.getPackageName());
        assertEquals("BoxWithAllConstructors", stringConstructor.getClassName());
        assertEquals(1, stringConstructor.getNumberOfParams());
        assertEquals("java.lang.String", stringConstructor.getParam(0).getType().describe());

        ResolvedConstructorDeclaration integerConstructor =
                compilationUnit.getConstructors().get(1);
        assertEquals("BoxWithAllConstructors", integerConstructor.getName());
        assertEquals("box.BoxWithAllConstructors.BoxWithAllConstructors", integerConstructor.getQualifiedName());
        assertEquals(1, integerConstructor.getNumberOfParams());
        assertEquals("box", integerConstructor.getPackageName());
        assertEquals("BoxWithAllConstructors", integerConstructor.getClassName());
        assertEquals(1, integerConstructor.getNumberOfParams());
        assertEquals(
                "java.lang.Integer", integerConstructor.getParam(0).getType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testNonCanonicalConstructor() {
        ReflectionRecordDeclaration compilationUnit =
                (ReflectionRecordDeclaration) typeSolver.solveType("box.BoxWithNonCanonicalConstructor");

        assertEquals(2, compilationUnit.getConstructors().size());

        ResolvedConstructorDeclaration integerConstructor =
                compilationUnit.getConstructors().get(0);
        assertEquals("BoxWithNonCanonicalConstructor", integerConstructor.getName());
        assertEquals(
                "box.BoxWithNonCanonicalConstructor.BoxWithNonCanonicalConstructor",
                integerConstructor.getQualifiedName());
        assertEquals(1, integerConstructor.getNumberOfParams());
        assertEquals("box", integerConstructor.getPackageName());
        assertEquals("BoxWithNonCanonicalConstructor", integerConstructor.getClassName());
        assertEquals(1, integerConstructor.getNumberOfParams());
        assertEquals(
                "java.lang.Integer", integerConstructor.getParam(0).getType().describe());

        ResolvedConstructorDeclaration stringConstructor =
                compilationUnit.getConstructors().get(1);

        assertEquals("BoxWithNonCanonicalConstructor", stringConstructor.getName());
        assertEquals(
                "box.BoxWithNonCanonicalConstructor.BoxWithNonCanonicalConstructor",
                stringConstructor.getQualifiedName());
        assertEquals(1, stringConstructor.getNumberOfParams());
        assertEquals("box", stringConstructor.getPackageName());
        assertEquals("BoxWithNonCanonicalConstructor", stringConstructor.getClassName());
        assertEquals(1, stringConstructor.getNumberOfParams());
        assertEquals("java.lang.String", stringConstructor.getParam(0).getType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void genericConstructorTest() {
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver(), typeSolver)))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);

        JavaParser javaParser = new JavaParser(configuration);
        ParseResult<CompilationUnit> cu = javaParser.parse("import box.GenericBox;\n"
                + "class Test {\n"
                + "  public static void main(String[] args) {\n"
                + "    GenericBox<Integer> box = new GenericBox<>(2);\n"
                + "    System.out.println(box.value());\n"
                + "  }\n"
                + "}");

        ObjectCreationExpr constructorInvocation =
                cu.getResult().get().findFirst(ObjectCreationExpr.class).get();

        assertEquals("GenericBox", constructorInvocation.getType().getNameAsString());
        assertEquals("box.GenericBox", constructorInvocation.getType().resolve().describe());
        assertEquals(
                "box.GenericBox", constructorInvocation.calculateResolvedType().describe());

        MethodCallExpr valueCall =
                Navigator.findMethodCall(cu.getResult().get(), "value").get();
        assertEquals("java.lang.Integer", valueCall.calculateResolvedType().describe());
    }

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_17)
    void testToStringShouldUseCorrectClassName() {
        ReflectionRecordDeclaration decl = (ReflectionRecordDeclaration) typeSolver.solveType("box.Box");

        String result = decl.toString();

        assertTrue(
                result.contains("ReflectionRecordDeclaration"),
                "Expected 'ReflectionRecordDeclaration' in toString(), but got: " + result);
    }
}
