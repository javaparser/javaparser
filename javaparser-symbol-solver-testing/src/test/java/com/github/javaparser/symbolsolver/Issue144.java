package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

import static org.junit.Assert.assertEquals;

public class Issue144 extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() throws IOException {
        File srcDir = adaptPath(new File("src/test/resources/issue144"));
        typeSolver = new JavaParserTypeSolver(srcDir);
    }

    @Test(expected = UnsolvedSymbolException.class)
    public void issue144() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue144/HelloWorld");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "HelloWorld");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("main").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        Expression firstParameter = methodCallExpr.getArgument(0);
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        javaParserFacade.solve(firstParameter).isSolved();
    }

    @Test
    public void issue144WithReflectionTypeSolver() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue144/HelloWorld");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "HelloWorld");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("main").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        Expression firstParameter = methodCallExpr.getArgument(0);
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new ReflectionTypeSolver(true));

        assertEquals(true, javaParserFacade.solve(firstParameter).isSolved());
    }

    @Test
    public void issue144WithCombinedTypeSolver() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue144/HelloWorld");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "HelloWorld");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("main").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        Expression firstParameter = methodCallExpr.getArgument(0);
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new CombinedTypeSolver(typeSolver, new ReflectionTypeSolver(true)));

        assertEquals(true, javaParserFacade.solve(firstParameter).isSolved());
    }
}
