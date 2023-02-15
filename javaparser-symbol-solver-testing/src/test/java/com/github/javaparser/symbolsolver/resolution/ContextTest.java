/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.resolution.*;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.*;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class ContextTest extends AbstractSymbolResolutionTest {

    private final TypeSolver typeSolver = new CombinedTypeSolver(new MemoryTypeSolver(), new ReflectionTypeSolver());

    private CompilationUnit parseSample(String sampleName) {
        InputStream is = ContextTest.class.getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        return StaticJavaParser.parse(is);
    }

    @Test
    void resolveDeclaredFieldReference() {
        CompilationUnit cu = parseSample("ReferencesToField");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToField");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method1");
        ExpressionStmt stmt = (ExpressionStmt) method1.getBody().get().getStatements().get(0);
        AssignExpr assignExpr = (AssignExpr) stmt.getExpression();

        Solver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertTrue(symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertTrue(symbolReference.getCorrespondingDeclaration().isField());
    }

    @Test
    void resolveInheritedFieldReference() {
        CompilationUnit cu = parseSample("ReferencesToField");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToFieldExtendingClass");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method2");
        ExpressionStmt stmt = (ExpressionStmt) method1.getBody().get().getStatements().get(0);
        AssignExpr assignExpr = (AssignExpr) stmt.getExpression();

        Solver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertTrue(symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertTrue(symbolReference.getCorrespondingDeclaration().isField());
    }

    @Test
    void resolveParameterReference() {
        CompilationUnit cu = parseSample("ReferencesToParameter");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferenceToParameter");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "aMethod");
        NameExpr foo = Navigator.findNameExpression(method1, "foo").get();

        Solver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference symbolReference = symbolSolver.solveSymbol("foo", foo);

        assertTrue(symbolReference.isSolved());
        assertEquals("foo", symbolReference.getCorrespondingDeclaration().getName());
        assertTrue(symbolReference.getCorrespondingDeclaration().isParameter());
    }

    @Test
    void resolveReferenceToImportedType() {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ResolvedClassDeclaration compilationUnitDecl = mock(ResolvedClassDeclaration.class);
        when(compilationUnitDecl.getName()).thenReturn("CompilationUnit");
        when(compilationUnitDecl.getQualifiedName()).thenReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.getSolvedJavaLangObject()).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).thenReturn(SymbolReference.solved(compilationUnitDecl));
        Solver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertTrue(ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceUsingQualifiedName() {
        CompilationUnit cu = parseSample("Navigator2");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ResolvedClassDeclaration compilationUnitDecl = mock(ResolvedClassDeclaration.class);
        when(compilationUnitDecl.getName()).thenReturn("CompilationUnit");
        when(compilationUnitDecl.getQualifiedName()).thenReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.getSolvedJavaLangObject()).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        //when(typeSolver.tryToSolveType("java.lang.com.github.javaparser.ast.CompilationUnit")).thenReturn(SymbolReference.unsolved(ClassDeclaration.class));
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).thenReturn(SymbolReference.solved(compilationUnitDecl));
        Solver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("com.github.javaparser.ast.CompilationUnit", param);

        assertTrue(ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceToClassesInTheSamePackage() {
        CompilationUnit cu = parseSample("Navigator3");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ResolvedClassDeclaration compilationUnitDecl = mock(ResolvedClassDeclaration.class);
        when(compilationUnitDecl.getName()).thenReturn("CompilationUnit");
        when(compilationUnitDecl.getQualifiedName()).thenReturn("my.packagez.CompilationUnit");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.getSolvedJavaLangObject()).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("my.packagez.CompilationUnit")).thenReturn(SymbolReference.solved(compilationUnitDecl));
        Solver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertTrue(ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("my.packagez.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceToClassInJavaLang() {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(1);

        ResolvedClassDeclaration stringDecl = mock(ResolvedClassDeclaration.class);
        when(stringDecl.getName()).thenReturn("String");
        when(stringDecl.getQualifiedName()).thenReturn("java.lang.String");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.getSolvedJavaLangObject()).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("me.tomassetti.symbolsolver.javaparser.String")).thenReturn(SymbolReference.unsolved());
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("java.lang.String")).thenReturn(SymbolReference.solved(stringDecl));
        Solver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("String", param);

        assertTrue(ref.isSolved());
        assertEquals("String", ref.getCorrespondingDeclaration().getName());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceToMethod() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToGetTypes = Navigator.findMethodCall(method, "getTypes").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver(true));
        Solver symbolSolver = new SymbolSolver(typeSolver);

        MethodUsage ref = symbolSolver.solveMethod("getTypes", Collections.emptyList(), callToGetTypes);

        assertEquals("getTypes", ref.getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.declaringType().getQualifiedName());

        //verify(typeSolver);
    }

    @Test
    void resolveCascadeOfReferencesToMethod() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToStream = Navigator.findMethodCall(method, "stream").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver(true));
        Solver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("stream", Collections.emptyList(), callToStream);

        assertEquals("stream", ref.getName());
        assertEquals("java.util.Collection", ref.declaringType().getQualifiedName());
    }

    @Test
    void resolveReferenceToMethodCalledOnArrayAccess() {
        CompilationUnit cu = parseSample("ArrayAccess");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "access");
        MethodCallExpr callToTrim = Navigator.findMethodCall(method, "trim").get();

        Path src = adaptPath("src/test/resources");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        Solver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("trim", Collections.emptyList(), callToTrim);

        assertEquals("trim", ref.getName());
        assertEquals("java.lang.String", ref.declaringType().getQualifiedName());
    }

    @Test
    void resolveReferenceToJreType() {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        com.github.javaparser.ast.type.Type streamJavaParserType = method.getParameters().get(0).getType();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType streamType = JavaParserFacade.get(typeSolver).convert(streamJavaParserType, method);

        assertEquals("java.util.stream.Stream<java.lang.String>", streamType.describe());
    }

    @Test
    void resolveReferenceToMethodWithLambda() {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr methodCallExpr = Navigator.findMethodCall(method, "filter").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType ref = JavaParserFacade.get(typeSolver).getType(methodCallExpr);

        assertEquals("java.util.stream.Stream<java.lang.String>", ref.describe());
        assertEquals(1, ref.asReferenceType().typeParametersValues().size());
        assertEquals("java.lang.String", ref.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    void resolveReferenceToLambdaParamBase() {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        NameExpr refToT = Navigator.findNameExpression(method, "t").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        ResolvedType ref = javaParserFacade.getType(refToT);

        assertEquals("? super java.lang.String", ref.describe());
    }

    @Test
    void resolveReferenceToLambdaParamSimplified() {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr call = Navigator.findMethodCall(method, "isEmpty").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        Solver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("isEmpty", Collections.emptyList(), call);

        assertEquals("isEmpty", ref.getName());
        assertEquals("java.lang.String", ref.declaringType().getQualifiedName());
    }

    @Test
    void resolveGenericReturnTypeOfMethodInJar() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr call = Navigator.findMethodCall(method, "getTypes").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("getTypes", methodUsage.getName());
        assertEquals("java.util.List<com.github.javaparser.ast.body.TypeDeclaration>", methodUsage.returnType().describe());
        assertEquals(1, methodUsage.returnType().asReferenceType().typeParametersValues().size());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", methodUsage.returnType().asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    void resolveCompoundGenericReturnTypeOfMethodInJar() throws IOException {
        CompilationUnit cu = parseSample("GenericClassNavigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "doubleTyped");
        MethodCallExpr call = Navigator.findMethodCall(method, "genericMethodWithDoubleTypedReturnType").get();

        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("genericMethodWithDoubleTypedReturnType", methodUsage.getName());
        assertEquals("java.util.Map<T, V>", methodUsage.returnType().describe());
    }

    @Test
    void resolveNestedGenericReturnTypeOfMethodInJar() throws IOException {
        CompilationUnit cu = parseSample("GenericClassNavigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nestedTyped");
        MethodCallExpr call = Navigator.findMethodCall(method, "genericMethodWithNestedReturnType").get();

        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("genericMethodWithNestedReturnType", methodUsage.getName());
        assertEquals("java.util.List<java.util.List<T>>", methodUsage.returnType().describe());
    }

    @Test
    void resolveSimpleGenericReturnTypeOfMethodInJar() throws IOException {
        CompilationUnit cu = parseSample("GenericClassNavigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "simple");
        MethodCallExpr call = Navigator.findMethodCall(method, "get").get();

        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("get", methodUsage.getName());
        assertEquals("java.util.List<java.util.List<java.lang.String>>", methodUsage.returnType().describe());
    }

    @Test
    void resolveGenericReturnTypeFromInputParam() throws IOException {
        CompilationUnit cu = parseSample("GenericClassNavigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "input");
        MethodCallExpr call = Navigator.findMethodCall(method, "copy").get();

        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("copy", methodUsage.getName());
        assertEquals("javaparser.GenericClass<java.util.List<java.lang.String>>", methodUsage.returnType().describe());
    }

    @Test
    void resolveComplexGenericReturnType() throws IOException {
        CompilationUnit cu = parseSample("GenericClassNavigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "complex");
        MethodCallExpr call = Navigator.findMethodCall(method, "complexGenerics").get();

        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("complexGenerics", methodUsage.getName());
        assertEquals("T", methodUsage.returnType().describe());
    }

    @Test
    void resolveDoubleNestedClassType() throws IOException {
        CompilationUnit cu = parseSample("GenericClassNavigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nestedTypes");
        MethodCallExpr call = Navigator.findMethodCall(method, "asList").get();

        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("asList", methodUsage.getName());
        assertEquals("java.util.List<javaparser.GenericClass.Bar.NestedBar>", methodUsage.getParamType(0).describe());
    }

    @Test
    void resolveTypeUsageOfFirstMethodInGenericClass() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetTypes = Navigator.findMethodCall(method, "getTypes").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage filterUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToGetTypes);

        assertEquals("java.util.List<com.github.javaparser.ast.body.TypeDeclaration>", filterUsage.returnType().describe());
        assertEquals(1, filterUsage.returnType().asReferenceType().typeParametersValues().size());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", filterUsage.returnType().asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    void resolveTypeUsageOfMethodInGenericClass() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToStream = Navigator.findMethodCall(method, "stream").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage filterUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToStream);

        assertEquals("java.util.stream.Stream<com.github.javaparser.ast.body.TypeDeclaration>", filterUsage.returnType().describe());
    }

    @Test
    void resolveTypeUsageOfCascadeMethodInGenericClass() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToFilter = Navigator.findMethodCall(method, "filter").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage filterUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToFilter);

        assertEquals("java.util.stream.Stream<com.github.javaparser.ast.body.TypeDeclaration>", filterUsage.returnType().describe());
    }

    @Test
    void resolveLambdaType() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToFilter = Navigator.findMethodCall(method, "filter").get();
        Expression lambdaExpr = callToFilter.getArguments().get(0);

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        ResolvedType typeOfLambdaExpr = JavaParserFacade.get(typeSolver).getType(lambdaExpr);

        assertEquals("java.util.function.Predicate<? super com.github.javaparser.ast.body.TypeDeclaration>", typeOfLambdaExpr.describe());
    }

    @Test
    void resolveReferenceToLambdaParam() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetName = Navigator.findMethodCall(method, "getName").get();
        Expression referenceToT = callToGetName.getScope().get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        ResolvedType typeOfT = JavaParserFacade.get(typeSolver).getType(referenceToT);

        assertEquals("? super com.github.javaparser.ast.body.TypeDeclaration", typeOfT.describe());
    }

    @Test
    void resolveReferenceToCallOnLambdaParam() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetName = Navigator.findMethodCall(method, "getName").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToGetName);

        assertEquals("getName", methodUsage.getName());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", methodUsage.declaringType().getQualifiedName());
    }

    @Test
    void resolveReferenceToOverloadMethodWithNullParam() {
        CompilationUnit cu = parseSample("OverloadedMethods");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m1");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded").get();

        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.String", ref.getParamTypes().get(0).describe());
    }

    @Test
    void resolveReferenceToOverloadMethodFindStricter() {
        CompilationUnit cu = parseSample("OverloadedMethods");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m2");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded").get();

        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.String", ref.getParamTypes().get(0).describe());
    }

    @Test
    void resolveReferenceToMethodWithGenericArrayTypeParam() {
        CompilationUnit cu = parseSample("GenericArrayMethodArgument");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericArrayMethodArgument");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        MethodCallExpr call = Navigator.findMethodCall(method, "foo").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("foo", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.String[]", ref.getParamType(0).describe());
    }

    @Test
    void resolveInheritedMethodFromInterface() {
        CompilationUnit cu = parseSample("InterfaceInheritance");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Test");
        MethodDeclaration method = Navigator.demandMethod(clazz, "test");
        MethodCallExpr call = Navigator.findMethodCall(method, "foobar").get();

        Path src = adaptPath("src/test/resources");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(src));
        ResolvedType type = JavaParserFacade.get(typeSolver).getType(call);

        assertEquals("double", type.describe());
    }

    @Test
    void resolveReferenceToOverloadMethodFindOnlyCompatible() {
        CompilationUnit cu = parseSample("OverloadedMethods");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m3");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded").get();

        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.Object", ref.getParamTypes().get(0).describe());
    }

    private <PS extends Node> PS parse(String code, ParseStart<PS> parseStart) {
        return parse(ParserConfiguration.LanguageLevel.JAVA_10, code, parseStart);
    }

    private <PS extends Node> PS parse(ParserConfiguration.LanguageLevel languageLevel, String code, ParseStart<PS> parseStart) {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLanguageLevel(languageLevel);
        ParseResult<PS> parseResult = new JavaParser(parserConfiguration).parse(parseStart, new StringProvider(code));
        if (!parseResult.isSuccessful()) {
            parseResult.getProblems().forEach(p -> System.out.println("ERR: " + p));
        }
        assertTrue(parseResult.isSuccessful());
        PS root = parseResult.getResult().get();
        return root;
    }

    @Test
    void localVariableDeclarationInScope() {
        String name = "a";
        CompilationUnit cu = parse(
                "class A {\n" + 
                "  void foo() {\n" +
                "    SomeClass a;\n" +
                "    a.aField;\n" +
                "  }\n" +
                "}", ParseStart.COMPILATION_UNIT);

        // The block statement expose to the 2nd statement the local var
        BlockStmt blockStmt = cu.findAll(BlockStmt.class).get(0);
        Context context1 = JavaParserFactory.getContext(blockStmt, typeSolver);
        assertEquals(1, context1.localVariablesExposedToChild(blockStmt.getStatement(1)).size());

        Node nameNode = cu.findAll(NameExpr.class).get(0);
        Context context = JavaParserFactory.getContext(nameNode, typeSolver);
        assertTrue(context.localVariableDeclarationInScope(name).isPresent());
    }
    
    @Test
    void localVariableDeclarationInScopeWithMultipleLocalesVariables() {
        String name = "a";
        CompilationUnit cu = parse(
                "class A {\n" + 
                "  void foo() {\n" +
                "    SomeClass a;\n" +
                "    SomeClass b;\n" +
                "    a.aField;\n" +
                "    SomeClass c;\n" +
                "    c.cField;\n" +
                "  }\n" +
                "}", ParseStart.COMPILATION_UNIT);

        // The block statement expose to the 2nd statement the local var
        BlockStmt blockStmt = cu.findAll(BlockStmt.class).get(0);
        Context context1 = JavaParserFactory.getContext(blockStmt, typeSolver);
        // verifying the number of variable defined before the statement a.aField 
        assertEquals(2, context1.localVariablesExposedToChild(blockStmt.getStatement(2)).size());
        // verifying the number of variable defined before the statement c.cField 
        assertEquals(3, context1.localVariablesExposedToChild(blockStmt.getStatement(4)).size());

        Node nameNode = cu.findAll(NameExpr.class).get(0);
        Context context = JavaParserFactory.getContext(nameNode, typeSolver);
        assertTrue(context.localVariableDeclarationInScope(name).isPresent());
    }

    //
    // Testing JLS 6.3 Scope of a Declaration
    //

    // The scope of a formal parameter of a method (§8.4.1), constructor (§8.8.1), or lambda expression (§15.27) is the
    // entire body of the method, constructor, or lambda expression.

    private void assertNoParamsExposedToChildInContextNamed(Node parent, Node child, String paramName) {
        assertNumberOfParamsExposedToChildInContextNamed(parent, child, paramName, 0, "the element is exposed and it should not");
    }

    private void assertOneParamExposedToChildInContextNamed(Node parent, Node child, String paramName) {
        assertNumberOfParamsExposedToChildInContextNamed(parent, child, paramName, 1, "the element is not exposed as expected");
    }

    private void assertNumberOfParamsExposedToChildInContextNamed(Node parent, Node child, String paramName,
                                                                  int expectedNumber, String message) {
        assertEquals(expectedNumber, JavaParserFactory.getContext(parent, typeSolver)
                .parametersExposedToChild(child).stream().filter(p -> p.getNameAsString().equals(paramName)).count(), "[" + paramName + "]: " + message);
    }

    private void assertNoVarsExposedToChildInContextNamed(Node parent, Node child, String paramName) {
        assertNumberOfVarsExposedToChildInContextNamed(parent, child, paramName, 0, "the element is exposed and it should not");
    }

    private void assertOneVarExposedToChildInContextNamed(Node parent, Node child, String paramName) {
        assertNumberOfVarsExposedToChildInContextNamed(parent, child, paramName, 1, "the element is not exposed as expected");
    }

    private void assertNumberOfVarsExposedToChildInContextNamed(Node parent, Node child, String paramName,
                                                                  int expectedNumber, String message) {
        List<VariableDeclarator> vars = JavaParserFactory.getContext(parent, typeSolver)
                .localVariablesExposedToChild(child);
        assertEquals(expectedNumber, vars.stream().filter(p -> p.getNameAsString().equals(paramName)).count(), "[" + paramName + "]: " + message);
    }

    private void assertNoPatternExprsExposedToImmediateParentInContextNamed(Node parent, String patternExprName, String message) {
        assertNumberOfPatternExprsExposedToImmediateParentInContextNamed(parent, patternExprName, 0, message);
    }
    private void assertOnePatternExprsExposedToImmediateParentInContextNamed(Node parent, String patternExprName, String message) {
        assertNumberOfPatternExprsExposedToImmediateParentInContextNamed(parent, patternExprName, 1, message);
    }
    private void assertNumberOfPatternExprsExposedToImmediateParentInContextNamed(Node parent, String patternExprName,
                                                                  int expectedNumber, String message) {
        List<PatternExpr> vars = JavaParserFactory.getContext(parent, typeSolver)
                .patternExprsExposedFromChildren();
        assertEquals(expectedNumber, vars.stream().filter(p -> p.getNameAsString().equals(patternExprName)).count(), "[" + patternExprName + "]: " + message);
    }

    private void assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(Node parent, String patternExprName, String message) {
        assertNumberOfNegatedPatternExprsExposedToImmediateParentInContextNamed(parent, patternExprName, 0, message);
    }
    private void assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(Node parent, String patternExprName, String message) {
        assertNumberOfNegatedPatternExprsExposedToImmediateParentInContextNamed(parent, patternExprName, 1, message);
    }
    private void assertNumberOfNegatedPatternExprsExposedToImmediateParentInContextNamed(Node parent, String patternExprName,
                                                                  int expectedNumber, String message) {
        List<PatternExpr> vars = JavaParserFactory.getContext(parent, typeSolver)
                .negatedPatternExprsExposedFromChildren();
        assertEquals(expectedNumber, vars.stream().filter(p -> p.getNameAsString().equals(patternExprName)).count(), "[" + patternExprName + "]: " + message);
    }

    @Test
    void parametersExposedToChildForMethod() {
        MethodDeclaration method = parse("void foo(int myParam) { aCall(); }",
                ParseStart.CLASS_BODY).asMethodDeclaration();
        assertOneParamExposedToChildInContextNamed(method, method.getBody().get(), "myParam");
        assertNoParamsExposedToChildInContextNamed(method, method.getType(), "myParam");
        assertNoParamsExposedToChildInContextNamed(method, method.getParameter(0), "myParam");
    }

    @Test
    void parametersExposedToChildForConstructor() {
        ConstructorDeclaration constructor = parse("Foo(int myParam) { aCall(); }",
                ParseStart.CLASS_BODY).asConstructorDeclaration();
        assertOneParamExposedToChildInContextNamed(constructor, constructor.getBody(), "myParam");
        assertNoParamsExposedToChildInContextNamed(constructor, constructor.getParameter(0), "myParam");
    }

    @Test
    void parametersExposedToChildForLambda() {
        LambdaExpr lambda = (LambdaExpr) parse("Object myLambda = (myParam) -> myParam * 2;",
                ParseStart.STATEMENT).asExpressionStmt().getExpression().asVariableDeclarationExpr()
                .getVariables().get(0).getInitializer().get();
        assertOneParamExposedToChildInContextNamed(lambda, lambda.getBody(), "myParam");
        assertNoParamsExposedToChildInContextNamed(lambda, lambda.getParameter(0), "myParam");
    }

    // The scope of a local variable declaration in a block (§14.4) is the rest of the block in which the declaration
    // appears, starting with its own initializer and including any further declarators to the right in the local
    // variable declaration statement.

    @Test
    void localVariablesExposedToChildWithinABlock() {
        BlockStmt blockStmt = parse("{ preStatement(); int a = 1, b = 2; otherStatement(); }",
                ParseStart.STATEMENT).asBlockStmt();
        assertNoVarsExposedToChildInContextNamed(blockStmt, blockStmt.getStatement(0), "a");
        assertNoVarsExposedToChildInContextNamed(blockStmt, blockStmt.getStatement(0), "b");
        assertOneVarExposedToChildInContextNamed(blockStmt, blockStmt.getStatement(2), "a");
        assertOneVarExposedToChildInContextNamed(blockStmt, blockStmt.getStatement(2), "b");

        VariableDeclarationExpr varDecl = blockStmt.getStatement(1).asExpressionStmt().getExpression()
                .asVariableDeclarationExpr();
        VariableDeclarator varA = varDecl.getVariables().get(0);
        VariableDeclarator varB = varDecl.getVariables().get(1);
        assertOneVarExposedToChildInContextNamed(varA,
                varA.getInitializer().get(), "a");
        assertOneVarExposedToChildInContextNamed(varDecl,
                varB, "a");
        assertNoVarsExposedToChildInContextNamed(varDecl,
                varA, "b");
    }

    // The scope of a local variable declared in the ForInit part of a basic for statement (§14.14.1) includes all of the following:
    // * Its own initializer
    // * Any further declarators to the right in the ForInit part of the for statement
    // * The Expression and ForUpdate parts of the for statement
    // * The contained Statement

    @Test
    void localVariablesExposedToChildWithinForStmt() {
        ForStmt forStmt = parse("for (int i=0, j=1;i<10;i++) { body(); }",
                ParseStart.STATEMENT).asForStmt();
        VariableDeclarationExpr initializations = forStmt.getInitialization().get(0).asVariableDeclarationExpr();
        assertOneVarExposedToChildInContextNamed(initializations,
                initializations.getVariable(1),
                "i");
        assertOneVarExposedToChildInContextNamed(forStmt,
                forStmt.getCompare().get(),
                "i");
        assertOneVarExposedToChildInContextNamed(forStmt,
                forStmt.getUpdate().get(0),
                "i");
        assertOneVarExposedToChildInContextNamed(forStmt,
                forStmt.getBody(),
                "i");
    }

    // The scope of a local variable declared in the FormalParameter part of an enhanced for statement (§14.14.2) is
    // the contained Statement.

    @Test
    void localVariablesExposedToChildWithinEnhancedForeachStmt() {
        ForEachStmt foreachStmt = parse("for (int i: myList) { body(); }",
                ParseStart.STATEMENT).asForEachStmt();
        assertOneVarExposedToChildInContextNamed(foreachStmt, foreachStmt.getBody(), "i");
        assertNoVarsExposedToChildInContextNamed(foreachStmt, foreachStmt.getVariable(), "i");
        assertNoVarsExposedToChildInContextNamed(foreachStmt, foreachStmt.getIterable(), "i");
    }

    // The scope of a parameter of an exception handler that is declared in a catch clause of a try statement (§14.20)
    // is the entire block associated with the catch.

    @Test
    void parametersExposedToChildWithinTryStatement() {
        CatchClause catchClause = parse("try {  } catch(Exception e) { body(); }",
                ParseStart.STATEMENT).asTryStmt().getCatchClauses().get(0);
        assertOneParamExposedToChildInContextNamed(catchClause, catchClause.getBody(), "e");
        assertNoParamsExposedToChildInContextNamed(catchClause, catchClause.getParameter(), "e");
    }

    // The scope of a variable declared in the ResourceSpecification of a try-with-resources statement (§14.20.3) is
    // from the declaration rightward over the remainder of the ResourceSpecification and the entire try block
    // associated with the try-with-resources statement.

    @Test
    void localVariablesExposedToChildWithinTryWithResourcesStatement() {
        TryStmt stmt = parse("try (Object res1 = foo(); Object res2 = foo()) { body(); }",
                ParseStart.STATEMENT).asTryStmt();
        assertOneVarExposedToChildInContextNamed(stmt, stmt.getResources().get(1), "res1");
        assertNoVarsExposedToChildInContextNamed(stmt, stmt.getResources().get(0), "res1");
        assertOneVarExposedToChildInContextNamed(stmt, stmt.getTryBlock(), "res1");
    }

    @Nested
    class PatternExprTests {
        @Test
        void instanceOfPatternExpr0() {
            InstanceOfExpr instanceOfExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String", ParseStart.EXPRESSION).asInstanceOfExpr();
            String message = "No Pattern Expr must be available from this expression.";
            assertNoPatternExprsExposedToImmediateParentInContextNamed(instanceOfExpr, "", message);
            assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(instanceOfExpr, "s", message);
        }

        @Test
        void instanceOfPatternExpr1() {
            String message = "Only s must be available from this expression.";
            InstanceOfExpr instanceOfExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s", ParseStart.EXPRESSION).asInstanceOfExpr();
            assertOnePatternExprsExposedToImmediateParentInContextNamed(instanceOfExpr, "s", message);
            assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(instanceOfExpr, "s", message);
        }

        @Test
        void instanceOfPatternExpr2() {
            String message = "Only s must be available from this enclosed expression.";
            EnclosedExpr enclosedExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "(a instanceof String s)", ParseStart.EXPRESSION).asEnclosedExpr();
            assertOnePatternExprsExposedToImmediateParentInContextNamed(enclosedExpr, "s", message);
            assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(enclosedExpr, "s", message);
        }

        @Test
        void instanceOfPatternExpr3() {
            String message = "Only s must be available from this multiple-enclosed expression.";
            EnclosedExpr enclosedExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "(((a instanceof String s)))", ParseStart.EXPRESSION).asEnclosedExpr();
            assertOnePatternExprsExposedToImmediateParentInContextNamed(enclosedExpr, "s", message);
            assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(enclosedExpr, "s", message);
        }

        @Test
        void patternExprPrint() {
            InstanceOfExpr instanceOfExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof final String s",
                    ParseStart.EXPRESSION).asInstanceOfExpr();
            assertEquals("final String s", instanceOfExpr.getPattern().get().toString());
        }


        @Nested
        class PatternExprNegationTests {
            @Test
            void instanceOfPatternExpr4() {
                String message = "Only s (NEGATED) must be available from this expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!(a instanceof String s)", ParseStart.EXPRESSION).asUnaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExpr5() {
                String message = "Only s must be available from this double-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!!(a instanceof String s)", ParseStart.EXPRESSION).asUnaryExpr();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", "Double negative means that it is true - it should be available.");
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExpr6() {
                String message = "Only s (NEGATED) must be available from this triple-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!!!(a instanceof String s)", ParseStart.EXPRESSION).asUnaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExpr7() {
                String message = "Only s must be available from this quadruple-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!!!!(a instanceof String s)", ParseStart.EXPRESSION).asUnaryExpr();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message + " -- " + "Double negative means that it is true - it should be available.");
            }
        }


        @Nested
        class PatternExprBinaryExprTests {

            @Test
            void instanceOfPatternExprBinaryExpr1() {
                String message = "Only s must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s == true", ParseStart.EXPRESSION).asBinaryExpr();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr2() {
                String message = "Only s must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "true == a instanceof String s", ParseStart.EXPRESSION).asBinaryExpr();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr3() {
                String message = "Only s (NEGATED) must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s == false", ParseStart.EXPRESSION).asBinaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr4() {
                String message = "Only s (NEGATED) must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "false == a instanceof String s", ParseStart.EXPRESSION).asBinaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr5() {
                String message = "Only s (NEGATED) must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s != true", ParseStart.EXPRESSION).asBinaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr5_negated() {
                String message = "Only s (NEGATED) must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s != true", ParseStart.EXPRESSION).asBinaryExpr();
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr5b() {
                String message = "Only s (NEGATED) must be available from this expression.";
                EnclosedExpr enclosedExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "(a instanceof String s != true)", ParseStart.EXPRESSION).asEnclosedExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(enclosedExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr5b_negated() {
                String message = "Only s (NEGATED) must be available from this expression.";
                EnclosedExpr enclosedExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "(a instanceof String s != true)", ParseStart.EXPRESSION).asEnclosedExpr();
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(enclosedExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr6() {
                String message = "Only s (NEGATED) must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s != false", ParseStart.EXPRESSION).asBinaryExpr();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr6_negated() {
                String message = "Only s (NEGATED) must be available from this expression.";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s != false", ParseStart.EXPRESSION).asBinaryExpr();
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr7() {
                String message = "Only s (NEGATED) must be available from this double-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!(a instanceof String s != true)", ParseStart.EXPRESSION).asUnaryExpr();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr7_negated() {
                String message = "Only s must be available from this double-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!(a instanceof String s != true)", ParseStart.EXPRESSION).asUnaryExpr();
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr8() {
                String message = "Only s must be available from this double-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!(a instanceof String s != false)", ParseStart.EXPRESSION).asUnaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr8_negated() {
                String message = "Only s must be available from this double-negated expression.";
                UnaryExpr unaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "!(a instanceof String s != false)", ParseStart.EXPRESSION).asUnaryExpr();
                assertOneNegatedPatternExprsExposedToImmediateParentInContextNamed(unaryExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprBinaryExpr9() {
                String message = "Must be no patterns available from this || expression (neither is guaranteed to be true).";
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "(a instanceof String s) || a instanceof String s2", ParseStart.EXPRESSION).asBinaryExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(binaryExpr, "s", message);
            }

        }


        @Nested
        class PatternExprVariableDeclarationTests {

            @Test
            void instanceOfPatternExprVariableDeclaration_variableDeclaration() {
                ExpressionStmt expressionStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "boolean x = a instanceof String s == true;", ParseStart.STATEMENT).asExpressionStmt();

                String message = "No pattern must be available outside of this variable declaration expression (note that the declaration expr contains many declarators).";
                VariableDeclarationExpr variableDeclarationExpr = expressionStmt.getExpression().asVariableDeclarationExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
            }

            @Test
            void instanceOfPatternExprVariableDeclaration_variableDeclarator() {
                ExpressionStmt expressionStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "boolean x = a instanceof String s == true;", ParseStart.STATEMENT).asExpressionStmt();

                String message = "No pattern must be available outside of this variable declaration expression (note that the declaration expr contains many declarators).";
                VariableDeclarationExpr variableDeclarationExpr = expressionStmt.getExpression().asVariableDeclarationExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);

                NodeList<VariableDeclarator> variables = variableDeclarationExpr.getVariables();
                assertEquals(1, variables.size(), "Expected 1 variable -- issue with test configuration/sample?");


                message = "No pattern must be available outside of this variable declarator (x).";
                VariableDeclarator variableDeclaratorX = variables.get(0);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclaratorX, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclaratorX, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclaratorX, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclaratorX, "s2", message);

            }

            @Test
            void instanceOfPatternExprVariableDeclaration_variableDeclaratorStatements1() {
                String x = "" +
                        "{\n" +
                        "    boolean x = a instanceof String s;\n" +
                        "    boolean result = s.contains(\"b\");\n" +
                        "}\n" +
                        "";
                BlockStmt blockStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.BLOCK).asBlockStmt();

                NodeList<Statement> statements = blockStmt.getStatements();
                assertEquals(2, statements.size(), "Expected 2 statements -- issue with test configuration/sample?");

                String message = "No pattern must be available outside of this statement.";
                Statement xStatement = statements.get(0);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(xStatement, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(xStatement, "s", message);

                Statement resultStatement = statements.get(1);
                Expression expression = resultStatement.asExpressionStmt().getExpression();
                VariableDeclarationExpr variableDeclarationExpr = expression.asVariableDeclarationExpr();

                Context context = JavaParserFactory.getContext(variableDeclarationExpr, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                assertFalse(s.isSolved(), "s is not available -- it is not definitively true when in a separate statement.");

            }

            @Test
            void instanceOfPatternExprVariableDeclaration_variableDeclaratorStatements2() {
                String x = "" +
                        "{\n" +
                        "    boolean x = (a instanceof String s);\n" +
                        "    boolean y = !(a instanceof String s);\n" +
                        "    boolean result = s.contains(\"b\");\n" +
                        "}\n" +
                        "";
                BlockStmt blockStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.BLOCK).asBlockStmt();

                NodeList<Statement> statements = blockStmt.getStatements();
                assertEquals(3, statements.size(), "Expected 3 statements -- issue with test configuration/sample?");

                String message;
                message = "No pattern must be available outside of this statement (x)";
                Statement xStatement = statements.get(0);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(xStatement, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(xStatement, "s", message);

                message = "No pattern must be available outside of this statement (y)";
                Statement yStatement = statements.get(1);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(yStatement, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(yStatement, "s", message);

                Statement resultStatement = statements.get(2);
                Expression expression = resultStatement.asExpressionStmt().getExpression();
                VariableDeclarationExpr variableDeclarationExpr = expression.asVariableDeclarationExpr();

                Context context = JavaParserFactory.getContext(variableDeclarationExpr, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                assertFalse(s.isSolved(), "s is not available -- it is not definitively true when in a separate statement.");
            }

            @Test
            void instanceOfPatternExprVariableDeclaration_variableDeclaratorStatements3() {
                String x = "" +
                        "{\n" +
                        "    boolean x = !(a instanceof String s);\n" +
                        "    boolean result = s.contains(\"b\");\n" +
                        "}\n" +
                        "";
                BlockStmt blockStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.BLOCK).asBlockStmt();

                NodeList<Statement> statements = blockStmt.getStatements();
                assertEquals(2, statements.size(), "Expected 2 statements -- issue with test configuration/sample?");

                String message = "No pattern must be available outside of this statement (x)";
                Statement xStatement = statements.get(0);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(xStatement, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(xStatement, "s", message);

                Statement resultStatement = statements.get(1);
                Expression expression = resultStatement.asExpressionStmt().getExpression();
                VariableDeclarationExpr variableDeclarationExpr = expression.asVariableDeclarationExpr();

                Context context = JavaParserFactory.getContext(variableDeclarationExpr, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                assertFalse(s.isSolved(), "s is not available -- it is not definitively true when in a separate statement.");

            }

        }


        @Nested
        class PatternExprScopeTests {

            @Test
            void instanceOfPatternExprResolution_expr1() {
                ExpressionStmt expressionStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "boolean x = a instanceof String s && a instanceof String s2;", ParseStart.STATEMENT).asExpressionStmt();

                String message = "No pattern must be available outside of this variable declaration expression (note that the declaration expr contains many declarators).";
                VariableDeclarationExpr variableDeclarationExpr = expressionStmt.getExpression().asVariableDeclarationExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s2", message);


                NodeList<VariableDeclarator> variables = variableDeclarationExpr.getVariables();
                assertEquals(1, variables.size(), "Expected 1 variable -- issue with test configuration/sample?");

                BinaryExpr binaryExpr = variables.get(0).getInitializer().get().asBinaryExpr();

                message = "Only s must be available from this declarator (left).";
                Expression leftBranch = binaryExpr.getLeft();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s2", message);

                message = "Only s2 must be available from this declarator (right).";
                Expression rightBranch = binaryExpr.getRight();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s", message);
                assertOnePatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s2", message);
            }

            @Test
            void instanceOfPatternExprResolution_expr2() {
                ExpressionStmt expressionStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "boolean x = !(a instanceof String s) && a instanceof String s2;", ParseStart.STATEMENT).asExpressionStmt();

                String message = "No pattern must be available outside of this variable declaration expression (note that the declaration expr contains many declarators).";
                VariableDeclarationExpr variableDeclarationExpr = expressionStmt.getExpression().asVariableDeclarationExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s2", message);

                // TODO: Assert pattern available from the binaryexpr
            }

            @Test
            void instanceOfPatternExprResolution_expr3() {
                ExpressionStmt expressionStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "boolean x = \"\" instanceof String s || \"\" instanceof String s2;", ParseStart.STATEMENT).asExpressionStmt();

//                String message = "Both s and s2 must be available from this declaration expression (AND).";
                String message = "No pattern must be available outside of this statement.";
                VariableDeclarationExpr variableDeclarationExpr = expressionStmt.getExpression().asVariableDeclarationExpr();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(variableDeclarationExpr, "s2", message);

                // TODO: Assert pattern available from the binaryexpr
            }

            @Test
            void instanceOfPatternExprResolution_expr_AND1() {
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s && s instanceof String s2", ParseStart.EXPRESSION).asBinaryExpr();

                String message;

                message = "Only s must be available from this declarator (left).";
                Expression leftBranch = binaryExpr.getLeft();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s2", message);

                message = "s and s2 must be available from this declarator (right).";
                Expression rightBranch = binaryExpr.getRight();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s", message);
                assertOnePatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s2", message);
            }

            @Test
            void instanceOfPatternExprResolution_expr_AND_solving1() {
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s && s instanceof String s2", ParseStart.EXPRESSION).asBinaryExpr();

                String message;

                message = "Only s must be available on the LEFT branch of an AND.";
                Expression leftBranch = binaryExpr.getLeft();
                Context leftBranchContext = JavaParserFactory.getContext(leftBranch, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> left_s = leftBranchContext.solveSymbol("s");
                assertTrue(left_s.isSolved());
                Optional<PatternExpr> optionalPatternExpr = leftBranchContext.patternExprInScope("s");
                SymbolReference<? extends ResolvedValueDeclaration> left_s2 = leftBranchContext.solveSymbol("s2");
                assertFalse(left_s2.isSolved());


                message = "s and s2 must be available on the RIGHT branch of an AND.";
                Expression rightBranch = binaryExpr.getRight();
                Context rightBranchContext = JavaParserFactory.getContext(rightBranch, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> right_s = rightBranchContext.solveSymbol("s");
                assertTrue(right_s.isSolved());
                SymbolReference<? extends ResolvedValueDeclaration> right_s2 = rightBranchContext.solveSymbol("s2");
                assertTrue(right_s2.isSolved());
            }

            @Test
            void instanceOfPatternExprResolution_expr_OR1() {
                BinaryExpr binaryExpr = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "a instanceof String s || s instanceof String s2", ParseStart.EXPRESSION).asBinaryExpr();

                String message;

                message = "Only s must be available from this declarator (left).";
                Expression leftBranch = binaryExpr.getLeft();
                assertOnePatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s", message);
                assertNoPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(leftBranch, "s2", message);

                message = "Only s2 must be available from this declarator (right).";
                Expression rightBranch = binaryExpr.getRight();
                assertNoPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s", message);
                assertOnePatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s2", message);
                assertNoNegatedPatternExprsExposedToImmediateParentInContextNamed(rightBranch, "s2", message);
            }


            @Test
            void instanceOfPatternExprResolution1() {
                CompilationUnit compilationUnit = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "class X { void x() { boolean foo = ((a instanceof String s) && s.length() > 0); } }", ParseStart.COMPILATION_UNIT);

                List<EnclosedExpr> enclosedExprs = compilationUnit.findAll(EnclosedExpr.class);
                assertEquals(2, enclosedExprs.size());

                EnclosedExpr enclosedExpr = enclosedExprs.get(0);

                List<NameExpr> nameExprs = enclosedExpr.findAll(NameExpr.class);
                assertEquals(2, nameExprs.size());

                NameExpr nameExpr = nameExprs.get(1);
                assertEquals("s", nameExpr.getNameAsString());

                Context context = JavaParserFactory.getContext(nameExpr, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> symbolReference = context.solveSymbol("s");

                assertTrue(symbolReference.isSolved(), "symbol not solved");
                ResolvedDeclaration correspondingDeclaration = symbolReference.getCorrespondingDeclaration();
                assertEquals("s", correspondingDeclaration.getName(), "unexpected name for the solved symbol");
                assertTrue(correspondingDeclaration.isPattern());
                assertEquals("s", correspondingDeclaration.asPattern().getName(), "unexpected name for the solved pattern");
                assertEquals("java.lang.String", correspondingDeclaration.asPattern().getType().asReferenceType().getQualifiedName(), "unexpected type for the solved pattern");

            }

            @Test
            void instanceOfPatternExprResolution1_negated() {
                CompilationUnit compilationUnit = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "class X { void x() { boolean foo = (!(a instanceof String s) && s.length() > 0); } }", ParseStart.COMPILATION_UNIT);

                List<EnclosedExpr> enclosedExprs = compilationUnit.findAll(EnclosedExpr.class);
                assertEquals(2, enclosedExprs.size());

                EnclosedExpr enclosedExpr = enclosedExprs.get(0);

                List<NameExpr> nameExprs = enclosedExpr.findAll(NameExpr.class);
                assertEquals(2, nameExprs.size());

                NameExpr nameExpr = nameExprs.get(1);
                assertEquals("s", nameExpr.getNameAsString());

                Context context = JavaParserFactory.getContext(nameExpr, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> symbolReference = context.solveSymbol("s");

                assertFalse(symbolReference.isSolved(), "symbol supposed to be not solved");
            }

            @Test
            void instanceOfPatternExprResolution2() {
                CompilationUnit compilationUnit = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, "class X { void x() { boolean foo = ((a instanceof String s) || s.length() > 0); } }", ParseStart.COMPILATION_UNIT);

                List<EnclosedExpr> enclosedExprs = compilationUnit.findAll(EnclosedExpr.class);
                assertEquals(2, enclosedExprs.size());

                EnclosedExpr enclosedExpr = enclosedExprs.get(0);

                List<NameExpr> nameExprs = enclosedExpr.findAll(NameExpr.class);
                assertEquals(2, nameExprs.size());

                NameExpr nameExpr = nameExprs.get(1);
                assertEquals("s", nameExpr.getNameAsString());

                Context context = JavaParserFactory.getContext(nameExpr, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> symbolReference = context.solveSymbol("s");

                assertFalse(symbolReference.isSolved(), "symbol supposed to be not solved");
            }

            @Nested
            class IfElse {


                @Test
                void instanceOfPattern_ifBlock1() {
                    String x = "" +
                            "if (a instanceof String s) {\n" +
                            "    result = s.contains(\"in scope\");\n" +
                            "}\n" +
                            "";
                    IfStmt ifStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.STATEMENT).asIfStmt();

                    List<MethodCallExpr> methodCallExprs = ifStmt.findAll(MethodCallExpr.class);
                    assertEquals(1, methodCallExprs.size());

                    MethodCallExpr methodCallExpr = methodCallExprs.get(0);
                    Context context = JavaParserFactory.getContext(methodCallExpr, typeSolver);

                    SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                    assertTrue(s.isSolved());
                    assertTrue(s.getCorrespondingDeclaration().isPattern());
                }

                @Test
                void instanceOfPattern_ifBlock1_noBraces() {
                    String x = "" +
                            "if (a instanceof String s) \n" +
                            "    result = s.contains(\"in scope\");\n" +
                            "\n" +
                            "";
                    IfStmt ifStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.STATEMENT).asIfStmt();

                    List<MethodCallExpr> methodCallExprs = ifStmt.findAll(MethodCallExpr.class);
                    assertEquals(1, methodCallExprs.size());

                    MethodCallExpr methodCallExpr = methodCallExprs.get(0);
                    Context context = JavaParserFactory.getContext(methodCallExpr, typeSolver);

                    SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                    assertTrue(s.isSolved());
                    assertTrue(s.getCorrespondingDeclaration().isPattern());
                }

                @Test
                void instanceOfPattern_ifBlock1_negatedCondition() {
                    String x = "" +
                            "if (!(a instanceof String s)) {\n" +
                            "    result = s.contains(\"NOT in scope\");\n" +
                            "}\n" +
                            "";
                    IfStmt ifStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.STATEMENT).asIfStmt();

                    List<MethodCallExpr> methodCallExprs = ifStmt.findAll(MethodCallExpr.class);
                    assertEquals(1, methodCallExprs.size());

                    MethodCallExpr methodCallExpr = methodCallExprs.get(0);
                    Context context = JavaParserFactory.getContext(methodCallExpr, typeSolver);

                    SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                    assertFalse(s.isSolved());
                }

                @Test
                void instanceOfPattern_ifBlock1_noBraces_negatedCondition() {
                    String x = "" +
                            "if (!(a instanceof String s)) \n" +
                            "    result = s.contains(\"NOT in scope\");\n" +
                            "\n" +
                            "";
                    IfStmt ifStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.STATEMENT).asIfStmt();

                    List<MethodCallExpr> methodCallExprs = ifStmt.findAll(MethodCallExpr.class);
                    assertEquals(1, methodCallExprs.size());

                    MethodCallExpr methodCallExpr = methodCallExprs.get(0);
                    Context context = JavaParserFactory.getContext(methodCallExpr, typeSolver);

                    SymbolReference<? extends ResolvedValueDeclaration> s = context.solveSymbol("s");
                    assertFalse(s.isSolved());
                }

                @Test
                void instanceOfPattern_ifElseBlock1() {
                    String x = "" +
                            "{\n" +
                            "    List s;\n" +
                            "    if (!(a instanceof String s)) {\n" +
                            "        result = s.contains(\"in scope\");\n" +
                            "    } else if (true) {\n" +
                            "        result = s.contains(\"in scope\");\n" +
                            "    }\n" +
                            "}\n" +
                            "";
                    BlockStmt blockStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.BLOCK).asBlockStmt();

                    List<MethodCallExpr> methodCallExprs = blockStmt.findAll(MethodCallExpr.class);
                    assertEquals(2, methodCallExprs.size());

                    // The first one should resolve to the standard variable (the list)
                    MethodCallExpr methodCallExpr_list = methodCallExprs.get(0);
                    Context context_list = JavaParserFactory.getContext(methodCallExpr_list, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_list = context_list.solveSymbol("s");
                    assertTrue(s_list.isSolved());
                    assertFalse(s_list.getCorrespondingDeclaration().isPattern());
//                    assertTrue(s_list.getCorrespondingDeclaration().isVariable()); // Should pass but seemingly not implemented/overridden, perhaps?

                    // The second one should resolve to the pattern variable (the string).
                    MethodCallExpr methodCallExpr_string = methodCallExprs.get(1);
                    Context context_string = JavaParserFactory.getContext(methodCallExpr_string, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string = context_string.solveSymbol("s");
                    assertTrue(s_string.isSolved());
                    assertTrue(s_string.getCorrespondingDeclaration().isPattern());
                }

                @Test
                void instanceOfPattern_ifElseBlock2() {
                    String x = "" +
                            "{\n" +
                            "    List s;\n" +
                            "    if (!(a instanceof String s)) {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    } else if (true) {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    } else if (true) {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    } else {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    }\n" +
                            "}\n" +
                            "";
                    BlockStmt blockStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.BLOCK).asBlockStmt();

                    List<MethodCallExpr> methodCallExprs = blockStmt.findAll(MethodCallExpr.class);
                    assertEquals(4, methodCallExprs.size());

                    // The first one should resolve to the standard variable (the list)
                    MethodCallExpr methodCallExpr_list = methodCallExprs.get(0);
                    Context context_list = JavaParserFactory.getContext(methodCallExpr_list, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_list = context_list.solveSymbol("s");
                    assertTrue(s_list.isSolved());
                    assertFalse(s_list.getCorrespondingDeclaration().isPattern());
//                    assertTrue(s_list.getCorrespondingDeclaration().isVariable()); // Should pass but seemingly not implemented/overridden, perhaps?

                    // The second one should resolve to the pattern variable (the string).
                    MethodCallExpr methodCallExpr_string = methodCallExprs.get(1);
                    Context context_string = JavaParserFactory.getContext(methodCallExpr_string, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string = context_string.solveSymbol("s");
                    assertTrue(s_string.isSolved());
                    assertTrue(s_string.getCorrespondingDeclaration().isPattern());

                    // The third one should resolve to the pattern variable (the string).
                    MethodCallExpr methodCallExpr_string2 = methodCallExprs.get(2);
                    Context context_string2 = JavaParserFactory.getContext(methodCallExpr_string2, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string2 = context_string2.solveSymbol("s");
                    assertTrue(s_string2.isSolved());
                    assertTrue(s_string2.getCorrespondingDeclaration().isPattern());

                    // The fourth one should resolve to the pattern variable (the string).
                    MethodCallExpr methodCallExpr_string3 = methodCallExprs.get(2);
                    Context context_string3 = JavaParserFactory.getContext(methodCallExpr_string3, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string3 = context_string3.solveSymbol("s");
                    assertTrue(s_string3.isSolved());
                    assertTrue(s_string3.getCorrespondingDeclaration().isPattern());
                }

                @Test
                void instanceOfPattern_ifElseBlock3() {
                    String x = "" +
                            "{\n" +
                            "    List s;\n" +
                            "    if (false) {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    } else if (!(a instanceof String s)) {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    } else if (true) {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    } else {\n" +
                            "        result = s.contains(\"\");\n" +
                            "    }\n" +
                            "}\n" +
                            "";
                    BlockStmt blockStmt = parse(ParserConfiguration.LanguageLevel.JAVA_14_PREVIEW, x, ParseStart.BLOCK).asBlockStmt();

                    List<MethodCallExpr> methodCallExprs = blockStmt.findAll(MethodCallExpr.class);
                    assertEquals(4, methodCallExprs.size());

                    // The first one should resolve to the standard variable (the list)
                    MethodCallExpr methodCallExpr_list = methodCallExprs.get(0);
                    Context context_list = JavaParserFactory.getContext(methodCallExpr_list, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_list = context_list.solveSymbol("s");
                    assertTrue(s_list.isSolved());
                    assertFalse(s_list.getCorrespondingDeclaration().isPattern());

                    // The second one should resolve to the standard variable (the list).
                    MethodCallExpr methodCallExpr_string = methodCallExprs.get(1);
                    Context context_string = JavaParserFactory.getContext(methodCallExpr_string, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string = context_string.solveSymbol("s");
                    assertTrue(s_string.isSolved());
                    assertFalse(s_string.getCorrespondingDeclaration().isPattern());

                    // The third one should resolve to the pattern variable (the string).
                    MethodCallExpr methodCallExpr_string2 = methodCallExprs.get(2);
                    Context context_string2 = JavaParserFactory.getContext(methodCallExpr_string2, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string2 = context_string2.solveSymbol("s");
                    assertTrue(s_string2.isSolved());
                    assertTrue(s_string2.getCorrespondingDeclaration().isPattern());

                    // The fourth one should resolve to the pattern variable (the string).
                    MethodCallExpr methodCallExpr_string3 = methodCallExprs.get(2);
                    Context context_string3 = JavaParserFactory.getContext(methodCallExpr_string3, typeSolver);
                    SymbolReference<? extends ResolvedValueDeclaration> s_string3 = context_string3.solveSymbol("s");
                    assertTrue(s_string3.isSolved());
                    assertTrue(s_string3.getCorrespondingDeclaration().isPattern());
                }
            }
        }

    }

}
