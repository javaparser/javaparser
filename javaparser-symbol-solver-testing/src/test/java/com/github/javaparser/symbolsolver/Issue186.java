package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;

public class Issue186 extends AbstractResolutionTest {

    @Test
    public void lambdaFlatMapIssue() {
        CompilationUnit cu = parseSample("Issue186");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "JavaTest");
        MethodDeclaration methodDeclaration = Navigator.demandMethod(clazz, "foo");
        MethodCallExpr methodCallExpr = Navigator.findMethodCall(methodDeclaration, "flatMap").get();
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        assertEquals("java.util.stream.Stream<java.lang.String>", javaParserFacade.getType(methodCallExpr).describe());

    }

    @Test
    public void lambdaPrimitivesIssue() {
        CompilationUnit cu = parseSample("Issue186");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "JavaTest");
        MethodDeclaration methodDeclaration = Navigator.demandMethod(clazz, "bar");
        List<LambdaExpr> lambdas = methodDeclaration.findAll(LambdaExpr.class);
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        assertEquals("java.util.function.Predicate<? super java.lang.String>", javaParserFacade.getType(lambdas.get(0)).describe());
        assertEquals("java.util.function.Function<? super java.lang.String, ? extends java.lang.Integer>", javaParserFacade.getType(lambdas.get(1)).describe());
        assertEquals("java.util.function.Predicate<? super java.lang.Integer>", javaParserFacade.getType(lambdas.get(2)).describe());

    }

}
