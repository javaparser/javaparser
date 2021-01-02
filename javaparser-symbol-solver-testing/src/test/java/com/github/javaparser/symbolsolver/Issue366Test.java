package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.FileNotFoundException;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue366Test extends AbstractResolutionTest {

    @Test()
    void test() throws FileNotFoundException {

        String code = "class A { int j = ~1;}";

        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = StaticJavaParser.parse(code);
        List<UnaryExpr> exprs = cu.findAll(UnaryExpr.class);
        exprs.forEach(expr -> {
            ResolvedType rt = expr.calculateResolvedType();
            assertEquals("int", rt.describe());
        });

    }

}
