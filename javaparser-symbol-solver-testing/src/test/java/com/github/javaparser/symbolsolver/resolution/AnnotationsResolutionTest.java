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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotationDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistAnnotationDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionAnnotationDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests resolution of annotation expressions.
 *
 * @author Malte Skoruppa
 */
class AnnotationsResolutionTest extends AbstractResolutionTest {

    @BeforeEach
    void configureSymbolSolver() throws IOException {
        // configure symbol solver before parsing
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @Test
    void solveJavaParserMarkerAnnotation() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CA");
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("foo.bar.MyAnnotation", resolved.getQualifiedName());
        assertEquals("foo.bar", resolved.getPackageName());
        assertEquals("MyAnnotation", resolved.getName());
    }

    @Test
    void solveJavaParserSingleMemberAnnotation() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CC");
        SingleMemberAnnotationExpr annotationExpr = (SingleMemberAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("foo.bar.MyAnnotationWithSingleValue", resolved.getQualifiedName());
        assertEquals("foo.bar", resolved.getPackageName());
        assertEquals("MyAnnotationWithSingleValue", resolved.getName());
    }
    
    @Test
    void solveJavaParserSingleMemberAnnotationAndDefaultvalue() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CF");
        NormalAnnotationExpr annotationExpr = (NormalAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        Expression memberValue = resolved.getAnnotationMembers().get(0).getDefaultValue();
        assertEquals(IntegerLiteralExpr.class, memberValue.getClass());
    }

    @Test
    void solveJavaParserNormalAnnotation() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CD");
        NormalAnnotationExpr annotationExpr = (NormalAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("foo.bar.MyAnnotationWithElements", resolved.getQualifiedName());
        assertEquals("foo.bar", resolved.getPackageName());
        assertEquals("MyAnnotationWithElements", resolved.getName());
    }

    @Test
    void solveReflectionMarkerAnnotation() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CA");
        MethodDeclaration method = Navigator.demandMethod(clazz, "equals");
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) method.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("java.lang.Override", resolved.getQualifiedName());
        assertEquals("java.lang", resolved.getPackageName());
        assertEquals("Override", resolved.getName());
    }
    
    @Test
    void solveReflectionMarkerAnnotationWithDefault() throws IOException {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CH");
        
        VariableDeclarator decl = Navigator.demandField(clazz, "field");
        FieldDeclaration fd = (FieldDeclaration)decl.getParentNode().get();
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) fd.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();
        // get default value
        Expression expr = resolved.getAnnotationMembers().get(0).getDefaultValue();
        assertEquals("BooleanLiteralExpr", expr.getClass().getSimpleName());
        assertEquals(true, ((BooleanLiteralExpr)expr).getValue());
        
        // resolve the type of the annotation member
        ResolvedType rt = resolved.getAnnotationMembers().get(0).getType();
        assertEquals("boolean", rt.describe());
    }

    @Test
    void solveReflectionSingleMemberAnnotation() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CC");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        SingleMemberAnnotationExpr annotationExpr =
                (SingleMemberAnnotationExpr) method.getBody().get().getStatement(0)
                        .asExpressionStmt().getExpression()
                        .asVariableDeclarationExpr().getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("java.lang.SuppressWarnings", resolved.getQualifiedName());
        assertEquals("java.lang", resolved.getPackageName());
        assertEquals("SuppressWarnings", resolved.getName());
    }

    @Test
    void solveJavassistMarkerAnnotation() throws IOException {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CA");
        MethodDeclaration method = Navigator.demandMethod(clazz, "setUp");
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) method.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("org.junit.Before", resolved.getQualifiedName());
        assertEquals("org.junit", resolved.getPackageName());
        assertEquals("Before", resolved.getName());
    }

    @Test
    void solveJavassistSingleMemberAnnotation() throws IOException {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CC");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testSomething");
        SingleMemberAnnotationExpr annotationExpr = (SingleMemberAnnotationExpr) method.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("org.junit.Ignore", resolved.getQualifiedName());
        assertEquals("org.junit", resolved.getPackageName());
        assertEquals("Ignore", resolved.getName());
    }

    @Test
    void solveJavassistNormalAnnotation() throws IOException {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CD");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testSomethingElse");
        NormalAnnotationExpr annotationExpr = (NormalAnnotationExpr) method.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("org.junit.Test", resolved.getQualifiedName());
        assertEquals("org.junit", resolved.getPackageName());
        assertEquals("Test", resolved.getName());
    }
    
    @Test
    void solveJavassistNormalAnnotationWithDefault() throws IOException {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CG");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testSomething");
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) method.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("org.junit.Ignore", resolved.getQualifiedName());
        Expression memberValue = resolved.getAnnotationMembers().get(0).getDefaultValue();
        assertEquals(StringLiteralExpr.class, memberValue.getClass());
        ResolvedType rt = resolved.getAnnotationMembers().get(0).getType();
        assertEquals("java.lang.String", rt.describe());
    }

    @Test
    void solveJavaParserMetaAnnotations() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CA");
        AnnotationExpr annotationExpr = clazz.getAnnotation(0);

        // resolve annotation expression @MyAnnotation
        JavaParserAnnotationDeclaration resolved = (JavaParserAnnotationDeclaration) annotationExpr.resolve();

        // check that the annotation @MyAnnotation has the annotations @Target and @Retention, but not @Documented
        assertEquals("foo.bar.MyAnnotation", resolved.getQualifiedName());
        assertTrue(resolved.hasDirectlyAnnotation("java.lang.annotation.Target"));
        assertTrue(resolved.hasDirectlyAnnotation("java.lang.annotation.Retention"));
        assertFalse(resolved.hasDirectlyAnnotation("java.lang.annotation.Documented"));
    }

    @Test
    void solveReflectionMetaAnnotations() {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CA");
        MethodDeclaration method = Navigator.demandMethod(clazz, "equals");
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) method.getAnnotation(0);

        // resolve annotation expression @Override
        ReflectionAnnotationDeclaration resolved = (ReflectionAnnotationDeclaration) annotationExpr.resolve();

        // check that the annotation @Override has the annotations @Target and @Retention, but not @Documented
        assertEquals("java.lang.Override", resolved.getQualifiedName());
        assertTrue(resolved.hasDirectlyAnnotation("java.lang.annotation.Target"));
        assertTrue(resolved.hasDirectlyAnnotation("java.lang.annotation.Retention"));
        assertFalse(resolved.hasDirectlyAnnotation("java.lang.annotation.Documented"));
    }

    @Test
    void solveJavassistMetaAnnotation() throws IOException {
        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CD");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testSomethingElse");
        AnnotationExpr annotationExpr = method.getAnnotation(0);

        // resolve annotation expression @Test
        JavassistAnnotationDeclaration resolved = (JavassistAnnotationDeclaration) annotationExpr.resolve();

        // check that the annotation @Test has the annotations @Target and @Retention, but not @Documented
        assertEquals("org.junit.Test", resolved.getQualifiedName());
        assertTrue(resolved.hasDirectlyAnnotation("java.lang.annotation.Target"));
        assertTrue(resolved.hasDirectlyAnnotation("java.lang.annotation.Retention"));
        assertFalse(resolved.hasDirectlyAnnotation("java.lang.annotation.Documented"));
    }

    @Test
    void solveQualifiedAnnotation() throws IOException {
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CE");
        AnnotationExpr annotationOnClass = clazz.getAnnotation(0);
        MethodDeclaration method = Navigator.demandMethod(clazz, "testSomething");
        AnnotationExpr annotationOnMethod = method.getAnnotation(0);

        ResolvedAnnotationDeclaration resolvedAnnotationOnClass = annotationOnClass.resolve();
        ResolvedAnnotationDeclaration resolvedAnnotationOnMethod = annotationOnMethod.resolve();

        assertEquals("foo.bar.MyAnnotation", resolvedAnnotationOnClass.getQualifiedName());
        assertEquals("org.junit.Ignore", resolvedAnnotationOnMethod.getQualifiedName());
    }

    @Test
    void solveQualifiedAnnotationWithReferenceTypeHasAnnotationAsWell() throws IOException {
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CE");
        ResolvedReferenceTypeDeclaration referenceType = clazz.resolve();

        boolean hasAnnotation = referenceType.hasAnnotation("org.junit.runner.RunWith");

        assertTrue(hasAnnotation, "org.junit.runner.RunWith not found on reference type");
    }

    @Test
    void solveAnnotationAncestor() throws IOException {
        CompilationUnit cu = parseSample("Annotations");
        AnnotationDeclaration ad = Navigator.findType(cu, "MyAnnotation").get().asAnnotationDeclaration();
        ResolvedReferenceTypeDeclaration referenceType = ad.resolve();

        List<ResolvedReferenceType> ancestors = referenceType.getAncestors();
        assertEquals(ancestors.size(), 1);
        assertEquals(ancestors.get(0).getQualifiedName(), "java.lang.annotation.Annotation");
    }

    @Test
    void solvePrimitiveAnnotationMember() throws IOException {
        CompilationUnit cu = parseSample("Annotations");
        AnnotationDeclaration ad = Navigator.findType(cu, "MyAnnotationWithSingleValue").get().asAnnotationDeclaration();
        assertEquals(ad.getMember(0).asAnnotationMemberDeclaration().resolve().getType().asPrimitive().describe(), "int");
    }

    @Test
    void solveInnerClassAnnotationMember() throws IOException {
        CompilationUnit cu = parseSample("Annotations");
        AnnotationDeclaration ad = Navigator.findType(cu, "MyAnnotationWithInnerClass").get().asAnnotationDeclaration();
        ResolvedAnnotationMemberDeclaration am = ad.getMember(0).asAnnotationMemberDeclaration().resolve();
        assertEquals(am.getType().asReferenceType().getQualifiedName(), "foo.bar.MyAnnotationWithInnerClass.MyInnerClass");
    }

}
