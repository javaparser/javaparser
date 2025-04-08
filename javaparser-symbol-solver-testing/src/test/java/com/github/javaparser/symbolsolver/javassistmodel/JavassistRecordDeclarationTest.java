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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclarationTest;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableSet;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Function;
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

        ResolvedFieldDeclaration valueField = compilationUnit.getField("value");
        assertEquals("T", valueField.getType().describe());
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

    @Test
    void testGetImplicitConstructor() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");

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
    void testGetExplicitConstructors() {
        JavassistRecordDeclaration compilationUnit =
                (JavassistRecordDeclaration) typeSolver.solveType("box.BoxWithAllConstructors");

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
    void testNonCanonicalConstructor() {
        JavassistRecordDeclaration compilationUnit =
                (JavassistRecordDeclaration) typeSolver.solveType("box.BoxWithNonCanonicalConstructor");

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

    @Test
    @EnabledForJreRange(min = org.junit.jupiter.api.condition.JRE.JAVA_14)
    public void testSolveMethod() {
        JavassistRecordDeclaration compilationUnit = (JavassistRecordDeclaration) typeSolver.solveType("box.Box");
        ResolvedType functionType = new SymbolSolver(typeSolver).classToResolvedType(Function.class);
        SymbolReference<ResolvedMethodDeclaration> method =
                compilationUnit.solveMethod("map", Collections.singletonList(functionType), false);
        assertTrue(method.isSolved());
        assertEquals(
                "box.Box.map(java.util.function.Function<T, U>)",
                method.getCorrespondingDeclaration().getQualifiedSignature());
    }
}
