package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;
import org.junit.jupiter.api.condition.JRE;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

public class Issue3976Test extends AbstractResolutionTest {

    @Test
    @EnabledForJreRange(min = JRE.JAVA_9)
    void test() {
        String testCase =
                "import java.util.Map;\n"
                + "public class Foo {\n"
                + "        public Object m() {\n"
                + "            return Map.of(\"k0\", 0, \"k1\", 1D);\n"
                + "        }\n"
                + "}";

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(testCase);

        MethodCallExpr methodCallExpr = cu.findFirst(MethodCallExpr.class).get();

        ResolvedType rt = methodCallExpr.calculateResolvedType();
        assertEquals("java.util.Map<java.lang.String, java.lang.Number>", rt.describe());
    }
}
