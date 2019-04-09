/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.*;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class ContextTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver = new CombinedTypeSolver(new MemoryTypeSolver(), new ReflectionTypeSolver());

    private CompilationUnit parseSample(String sampleName) {
        InputStream is = ContextTest.class.getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        return StaticJavaParser.parse(is);
    }

    @Test
    void resolveDeclaredFieldReference() {
        CompilationUnit cu = parseSample("ReferencesToField");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToField");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method1");
        ExpressionStmt stmt = (ExpressionStmt) method1.getBody().get().getStatements().get(0);
        AssignExpr assignExpr = (AssignExpr) stmt.getExpression();

        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertTrue(symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertTrue(symbolReference.getCorrespondingDeclaration().isField());
    }

    @Test
    void resolveInheritedFieldReference() {
        CompilationUnit cu = parseSample("ReferencesToField");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToFieldExtendingClass");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method2");
        ExpressionStmt stmt = (ExpressionStmt) method1.getBody().get().getStatements().get(0);
        AssignExpr assignExpr = (AssignExpr) stmt.getExpression();

        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertTrue(symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertTrue(symbolReference.getCorrespondingDeclaration().isField());
    }

    @Test
    void resolveParameterReference() {
        CompilationUnit cu = parseSample("ReferencesToParameter");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferenceToParameter");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "aMethod");
        NameExpr foo = Navigator.findNameExpression(method1, "foo").get();

        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference symbolReference = symbolSolver.solveSymbol("foo", foo);

        assertTrue(symbolReference.isSolved());
        assertEquals("foo", symbolReference.getCorrespondingDeclaration().getName());
        assertTrue(symbolReference.getCorrespondingDeclaration().isParameter());
    }

    @Test
    void resolveReferenceToImportedType() {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ResolvedClassDeclaration compilationUnitDecl = mock(ResolvedClassDeclaration.class);
        when(compilationUnitDecl.getName()).thenReturn("CompilationUnit");
        when(compilationUnitDecl.getQualifiedName()).thenReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).thenReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertTrue(ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceUsingQualifiedName() {
        CompilationUnit cu = parseSample("Navigator2");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ResolvedClassDeclaration compilationUnitDecl = mock(ResolvedClassDeclaration.class);
        when(compilationUnitDecl.getName()).thenReturn("CompilationUnit");
        when(compilationUnitDecl.getQualifiedName()).thenReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = mock(TypeSolver.class);
        //when(typeSolver.tryToSolveType("java.lang.com.github.javaparser.ast.CompilationUnit")).thenReturn(SymbolReference.unsolved(ClassDeclaration.class));
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).thenReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        
        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("com.github.javaparser.ast.CompilationUnit", param);

        assertTrue(ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceToClassesInTheSamePackage() {
        CompilationUnit cu = parseSample("Navigator3");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ResolvedClassDeclaration compilationUnitDecl = mock(ResolvedClassDeclaration.class);
        when(compilationUnitDecl.getName()).thenReturn("CompilationUnit");
        when(compilationUnitDecl.getQualifiedName()).thenReturn("my.packagez.CompilationUnit");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("my.packagez.CompilationUnit")).thenReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertTrue(ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("my.packagez.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceToClassInJavaLang() {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(1);

        ResolvedClassDeclaration stringDecl = mock(ResolvedClassDeclaration.class);
        when(stringDecl.getName()).thenReturn("String");
        when(stringDecl.getQualifiedName()).thenReturn("java.lang.String");
        TypeSolver typeSolver = mock(TypeSolver.class);
        when(typeSolver.tryToSolveType("me.tomassetti.symbolsolver.javaparser.String")).thenReturn(SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class));
        when(typeSolver.getRoot()).thenReturn(typeSolver);
        when(typeSolver.solveType("java.lang.Object")).thenReturn(new ReflectionClassDeclaration(Object.class, typeSolver));
        when(typeSolver.tryToSolveType("java.lang.String")).thenReturn(SymbolReference.solved(stringDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);

        SymbolReference<? extends ResolvedTypeDeclaration> ref = symbolSolver.solveType("String", param);

        assertTrue(ref.isSolved());
        assertEquals("String", ref.getCorrespondingDeclaration().getName());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    void resolveReferenceToMethod() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToGetTypes = Navigator.findMethodCall(method, "getTypes").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver(true));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);

        MethodUsage ref = symbolSolver.solveMethod("getTypes", Collections.emptyList(), callToGetTypes);

        assertEquals("getTypes", ref.getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.declaringType().getQualifiedName());

        //verify(typeSolver);
    }

    @Test
    void resolveCascadeOfReferencesToMethod() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToStream = Navigator.findMethodCall(method, "stream").get();

        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver(true));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("stream", Collections.emptyList(), callToStream);

        assertEquals("stream", ref.getName());
        assertEquals("java.util.Collection", ref.declaringType().getQualifiedName());
    }

    @Test
    void resolveReferenceToMethodCalledOnArrayAccess() {
        CompilationUnit cu = parseSample("ArrayAccess");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "access");
        MethodCallExpr callToTrim = Navigator.findMethodCall(method, "trim").get();

        Path src = adaptPath("src/test/resources");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("trim", Collections.emptyList(), callToTrim);

        assertEquals("trim", ref.getName());
        assertEquals("java.lang.String", ref.declaringType().getQualifiedName());
    }

    @Test
    void resolveReferenceToJreType() {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        com.github.javaparser.ast.type.Type streamJavaParserType = method.getParameters().get(0).getType();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType streamType = JavaParserFacade.get(typeSolver).convert(streamJavaParserType, method);

        assertEquals("java.util.stream.Stream<java.lang.String>", streamType.describe());
    }

    @Test
    void resolveReferenceToMethodWithLambda() {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr call = Navigator.findMethodCall(method, "isEmpty").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("isEmpty", Collections.emptyList(), call);

        assertEquals("isEmpty", ref.getName());
        assertEquals("java.lang.String", ref.declaringType().getQualifiedName());
    }

    @Test
    void resolveGenericReturnTypeOfMethodInJar() throws IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericClassNavigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Test");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m3");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded").get();

        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.Object", ref.getParamTypes().get(0).describe());
    }

    private <PS extends Node> PS parse(String code, ParseStart<PS> parseStart) {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_10);
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
        CompilationUnit cu = parse("class A { void foo() {\n" +
                "SomeClass a; a.aField;" + "\n" +
                "} }", ParseStart.COMPILATION_UNIT);

        // The block statement expose to the 2nd statement the local var
        BlockStmt blockStmt = cu.findAll(BlockStmt.class).get(0);
        Context context1 = JavaParserFactory.getContext(blockStmt, typeSolver);
        assertEquals(1, context1.localVariablesExposedToChild(blockStmt.getStatement(1)).size());

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
                .parametersExposedToChild(child).stream().filter(p -> p.getNameAsString().equals(paramName)).count(), message);
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
        assertEquals(expectedNumber, vars.stream().filter(p -> p.getNameAsString().equals(paramName)).count(), message);
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
        LambdaExpr lambda = (LambdaExpr)parse("Object myLambda = (myParam) -> myParam * 2;",
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

}
