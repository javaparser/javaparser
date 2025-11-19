package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

public class Issue2738Test extends AbstractSymbolResolutionTest {
    @Test
    void test() throws IOException {
        ParserConfiguration config = new ParserConfiguration();
        Path pathToSourceFile = adaptPath("src/test/resources/issue2738");
        TypeSolver cts = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(pathToSourceFile));
        config.setSymbolResolver(new JavaSymbolSolver(cts));

        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = StaticJavaParser.parse(pathToSourceFile.resolve("B.java"));

        // We shouldn't throw an exception
        assertDoesNotThrow(() -> cu.findAll(MethodCallExpr.class).stream().map(MethodCallExpr::resolve));
    }
}
