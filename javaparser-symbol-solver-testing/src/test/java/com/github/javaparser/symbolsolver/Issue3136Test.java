package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3136Test extends AbstractResolutionTest {

    @Test
    void test() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String s =
                "public class Program {\n" +
                        "\n" +
                        "    public class InnerClass {\n" +
                        "    }\n" +
                        "\n" +
                        "    {\n" +
                        "        this.new InnerClass();\n" +
                        "    }\n" +
                        "}";

        CompilationUnit cu = StaticJavaParser.parse(s);
        List<ThisExpr> exprs = cu.findAll(ThisExpr.class);
        exprs.forEach(expr-> {
            assertEquals("Program",expr.calculateResolvedType().describe());
            assertEquals("Program",expr.resolve().getQualifiedName());
        });
    }
}
