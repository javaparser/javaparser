package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3614Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = "package java./*aaaaa*/util;\n"
                + "class Foo {\n"
                + "  public void test() {\n"
                + "        ArrayList list = new ArrayList();\n"
                + "    }"
                + "}";

        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        StaticJavaParser.setConfiguration(configuration);

        CompilationUnit cu = StaticJavaParser.parse(code);

        VariableDeclarationExpr vde = cu.findFirst(VariableDeclarationExpr.class).get();
        String resolvedType = vde.calculateResolvedType().describe();
        assertEquals("java.util.ArrayList", resolvedType);
    }
}
