package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotationDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistAnnotationDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionAnnotationDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests resolution of annotation expressions.
 *
 * @author Malte Skoruppa
 */
class AnnotationsResolutionTest extends AbstractResolutionTest {

    @BeforeAll
    static void configureSymbolSolver() throws IOException {
        // configure symbol solver before parsing
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @AfterAll
    static void unConfigureSymbolSolver() {
        // unconfigure symbol solver so as not to potentially disturb tests in other classes
        StaticJavaParser.getConfiguration().setSymbolResolver(null);
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
}
