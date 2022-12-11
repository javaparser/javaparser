package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3024Test extends AbstractResolutionTest {


    @Test
    public void test() {
        StaticJavaParser.getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit parse = StaticJavaParser.parse("public class Test {\n" +
                "\n" +
                "    public static Test getInstance() {\n" +
                "        return new Test();\n" +
                "    }\n" +
                "\n" +
                "    public void validateBean() {\n" +
                "        Test.getInstance().new InnerClass();\n" +
                "    }\n" +
                "\n" +
                "    public class InnerClass {\n" +
                "        private boolean hasErrors;\n" +
                "    }\n" +
                "}");

        List<MethodCallExpr> methodCallExprList = parse.findAll(MethodCallExpr.class);
        for (MethodCallExpr methodCallExpr : methodCallExprList) {
            assertEquals("Test.getInstance",methodCallExpr.resolve().getQualifiedName());;
        }
    }

}
