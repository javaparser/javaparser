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

public class Issue4710Test {
    @Test
    void test() {
        String code = "class Foo<T> {}\n" + "public class Test<T> {\n"
                + "    void test(String s, Object... objects) { }\n"
                + "    void test(String s, Foo<T> f, Object... objects) { }\n"
                + "    void foo() {\n"
                + "        test(\"hello\", new Foo<Integer>());\n"
                + "    }\n"
                + "}";

        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        StaticJavaParser.setConfiguration(configuration);

        CompilationUnit cu = StaticJavaParser.parse(code);

        MethodCallExpr call = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration resolvedMethod = call.resolve();
        assertEquals(
                "Test.test(java.lang.String, Foo<T>, java.lang.Object...)", resolvedMethod.getQualifiedSignature());
    }
}
