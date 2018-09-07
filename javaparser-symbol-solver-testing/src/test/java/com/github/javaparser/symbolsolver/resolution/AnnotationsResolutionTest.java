package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserConstructorDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * Tests resolution of annotation expressions.
 *
 * @author Malte Skoruppa
 */
public class AnnotationsResolutionTest extends AbstractResolutionTest {

    @Test
    public void solveJavaParserMarkerAnnotation() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CA");
        MarkerAnnotationExpr annotationExpr = (MarkerAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("foo.bar.MyAnnotation", resolved.getQualifiedName());
    }

    @Test
    public void solveJavaParserSingleMemberAnnotation() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CC");
        SingleMemberAnnotationExpr annotationExpr = (SingleMemberAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("foo.bar.MyAnnotationWithSingleValue", resolved.getQualifiedName());
    }

    @Test
    public void solveJavaParserNormalAnnotation() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get annotation expression
        CompilationUnit cu = parseSample("Annotations");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "CD");
        NormalAnnotationExpr annotationExpr = (NormalAnnotationExpr) clazz.getAnnotation(0);

        // resolve annotation expression
        ResolvedAnnotationDeclaration resolved = annotationExpr.resolve();

        // check that the expected annotation declaration equals the resolved annotation declaration
        assertEquals("foo.bar.MyAnnotationWithFields", resolved.getQualifiedName());
    }
}
