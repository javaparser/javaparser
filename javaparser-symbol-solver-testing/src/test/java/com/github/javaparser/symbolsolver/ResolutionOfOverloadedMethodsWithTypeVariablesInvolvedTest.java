package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;

public class ResolutionOfOverloadedMethodsWithTypeVariablesInvolvedTest {

    @Test
    public void test() {
        String code = "public class Box<E> {\n" + "    private E element;\n"
                + "\n"
                + "    public Box(E element) {\n"
                + "        this.element = element;\n"
                + "    }\n"
                + "\n"
                + "    public E getElement() {return element;}\n"
                + "\n"
                + "    public void setElement(E element) {this.element = element;}\n"
                + "\n"
                + "    @Override\n"
                + "    public String toString() {\n"
                + "        StringBuilder builder = new StringBuilder();\n"
                + "        builder.append(\"Box [element=\");\n"
                + "        builder.append(element == this ? \"(this box)\" : element);\n"
                + "        builder.append(\"]\");\n"
                + "        return builder.toString();\n"
                + "    }\n"
                + "}";
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = StaticJavaParser.parse(code);

        final List<MethodCallExpr> methodCallExprs = cu.findAll(MethodCallExpr.class);

        List<String> expected = new ArrayList<>();
        expected.add("builder.append(\"Box [element=\")");
        expected.add(
                "ReflectionMethodDeclaration{method=public java.lang.StringBuilder java.lang.StringBuilder.append(java.lang.String)}");
        expected.add("builder.append(element == this ? \"(this box)\" : element)");
        expected.add(
                "ReflectionMethodDeclaration{method=public java.lang.StringBuilder java.lang.StringBuilder.append(java.lang.Object)}");
        expected.add("builder.append(\"]\")");
        expected.add(
                "ReflectionMethodDeclaration{method=public java.lang.StringBuilder java.lang.StringBuilder.append(java.lang.String)}");
        expected.add("builder.toString()");
        expected.add("ReflectionMethodDeclaration{method=public java.lang.String java.lang.StringBuilder.toString()}");

        List<String> result = new ArrayList<>();
        for (MethodCallExpr methodCallExpr : methodCallExprs) {
            final String expr = methodCallExpr.toString();
            result.add(expr);
            final String methodDeclaration = methodCallExpr.resolve().toString();
            result.add(methodDeclaration);
        }

        assertEquals(expected, result);
    }
}
