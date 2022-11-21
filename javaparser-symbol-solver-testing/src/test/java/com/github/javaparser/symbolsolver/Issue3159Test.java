package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3159Test extends AbstractResolutionTest {

    @Test
    public void test() throws IOException {
        String code = "class Test {\n" +
                "  void f() {\n" +
                "    int a = 0;\n" +
                "    while (a < 10) {}\n" +
                "  }\n" +
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(code);
        NameExpr mce = cu.findFirst(NameExpr.class).get();

        ResolvedValueDeclaration v = mce.resolve();
        // verify that the symbol declaration represents a variable
        assertTrue(v.isVariable());
    }

}
