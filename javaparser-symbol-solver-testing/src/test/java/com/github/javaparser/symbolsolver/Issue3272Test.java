package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3272Test {

    @Test
    void test0() {
        // Source code
        String sourceCode = "import java.util.function.Consumer;" +
                "class A {" +
                "   Consumer<Integer> consumer = item -> {};" +
                "}";
        // Setup symbol solver
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        // Setup parser
        JavaParser parser = new JavaParser(configuration);
        CompilationUnit cu = parser.parse(sourceCode).getResult().get();
        // Test
        LambdaExpr expr = Navigator.demandNodeOfGivenClass(cu, LambdaExpr.class);
        ResolvedType type = expr.calculateResolvedType();
        assertEquals("java.util.function.Consumer<java.lang.Integer>", type.describe());
    }

    @Test
    void test1() {
        // Source code
        String sourceCode = "import java.util.function.Consumer;" +
                "class A {" +
                "   Consumer<Integer> consumer;" +
                "   {" +
                "       consumer = item -> {};" +
                "   }" +
                "}";
        // Setup symbol solver
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        // Setup parser
        JavaParser parser = new JavaParser(configuration);
        CompilationUnit cu = parser.parse(sourceCode).getResult().get();
        // Test
        LambdaExpr expr = Navigator.demandNodeOfGivenClass(cu, LambdaExpr.class);
        ResolvedType type = expr.calculateResolvedType();
        assertEquals("java.util.function.Consumer<java.lang.Integer>", type.describe());
    }

}
