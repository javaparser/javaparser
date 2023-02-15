package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3859Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = "import java.util.function.Consumer;\n" +
                "\n" +
                "class Demo {\n" +
                "    void foo(Consumer<String> arg) {}\n" +
                "    void print(Object arg) {}\n" +
                "    public void bar() {\n" +
                "        foo(s->print(s));\n" +
                "    }\n" +
                "    public void baz() {\n" +
                "        foo((s->print(s)));\n" +
                "    }\n" +
                "}\n";
        CompilationUnit cu = JavaParserAdapter.of(
                createParserWithResolver(defaultTypeSolver())).parse(code);

        List<LambdaExpr> lambdas = cu.findAll(LambdaExpr.class);
        assertEquals(2, lambdas.size());
        assertEquals("java.util.function.Consumer<java.lang.String>",
                lambdas.get(0).calculateResolvedType().describe());
        // Before the fix the following statement failed with an
        // `UnsupportedOperationException` because an extra `(...)` around
        // an argument wasn't handled.
        assertEquals("java.util.function.Consumer<java.lang.String>",
                lambdas.get(1).calculateResolvedType().describe());

        List<NameExpr> exprs = cu.findAll(NameExpr.class);
        assertEquals(2, exprs.size());
        assertEquals("? super java.lang.String",
                exprs.get(0).calculateResolvedType().describe());
        // Before the fix the following statement failed with an
        // `UnsupportedOperationException` because an extra `(...)` around
        // an argument wasn't handled.
        assertEquals("? super java.lang.String",
                exprs.get(1).calculateResolvedType().describe());
    }
}
