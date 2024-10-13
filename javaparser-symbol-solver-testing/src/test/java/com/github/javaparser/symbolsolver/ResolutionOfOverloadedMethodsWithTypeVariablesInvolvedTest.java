package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.Test;

public class ResolutionOfOverloadedMethodsWithTypeVariablesInvolvedTest {

    @Test
    void test() {
        String code = "public class Box<E> {\n"
                + "    private E element;\n"
                + "\n"
                + "    public Box(E element) {\n"
                + "        this.element = element;\n"
                + "    }\n"
                + "\n"
                + "    @Override\n"
                + "    public String toString() {\n"
                + "        StringBuilder builder = new StringBuilder();\n"
                + "        builder.append(element == this ? \"(this box)\" : element);\n"
                + "        return builder.toString();\n"
                + "    }\n"
                + "}";
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = StaticJavaParser.parse(code);

        final List<MethodCallExpr> methodCallExprs = cu.findAll(MethodCallExpr.class);
        MethodCallExpr methodCallExpr = methodCallExprs.get(0);
        assertEquals("builder.append(element == this ? \"(this box)\" : element)", methodCallExpr.toString());
        assertEquals("append", methodCallExpr.resolve().getName());
        assertEquals(
                "java.lang.Object",
                methodCallExpr.resolve().getParam(0).getType().describe());
    }
}
