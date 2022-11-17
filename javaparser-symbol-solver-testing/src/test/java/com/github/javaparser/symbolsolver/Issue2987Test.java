package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2987Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = "class ClassA {\n" +
                "    void f() {\n" +
                "        String s = \"\";\n" +
                "        String t = (s.length() == 0 ? \"*\" : s) + \"\" ;\n" +
                "    }\n" +
                "}";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(code);

        MethodCallExpr expr = cu.findFirst(MethodCallExpr.class).get();
        assertEquals("java.lang.String.length()", expr.resolve().getQualifiedSignature());

    }

}
