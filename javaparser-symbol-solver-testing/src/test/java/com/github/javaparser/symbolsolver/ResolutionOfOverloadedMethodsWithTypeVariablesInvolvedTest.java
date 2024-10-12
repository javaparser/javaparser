package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.Test;

public class ResolutionOfOverloadedMethodsWithTypeVariablesInvolvedTest {

    public static final String EXPR = "builder.append(element == this ? \"(this box)\" : element)";
    public static final String METHOD_NAME = "append";
    public static final String PARAM_TYPE = "java.lang.Object";

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
        assertEquals(EXPR, methodCallExpr.toString());
        assertEquals(METHOD_NAME, methodCallExpr.resolve().getName());
        assertEquals(PARAM_TYPE, methodCallExpr.resolve().getParam(0).getType().describe());
    }
}
