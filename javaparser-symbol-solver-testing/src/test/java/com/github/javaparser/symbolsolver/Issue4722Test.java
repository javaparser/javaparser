package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue4722Test {
    @Test
    void test() {
        String code = "public class Test {\n" + "    void test(String s, Object... objects) { }\n"
                + "    void test(String s, String t, Object... objects) { }\n"
                + "    void foo() {\n"
                + "        test(\"hello\", \"world\");\n"
                + "    }\n"
                + "}";

        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        StaticJavaParser.setConfiguration(configuration);

        CompilationUnit cu = StaticJavaParser.parse(code);

        MethodCallExpr call = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration resolvedMethod = call.resolve();
        assertEquals(
                "Test.test(java.lang.String, java.lang.String, java.lang.Object...)",
                resolvedMethod.getQualifiedSignature());
    }
}
