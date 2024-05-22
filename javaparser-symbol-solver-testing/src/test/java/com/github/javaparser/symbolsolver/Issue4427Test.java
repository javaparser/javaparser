package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

public class Issue4427Test extends AbstractSymbolResolutionTest {
  @Test
  public void testIssue4427() throws IOException {
    Path issueResourcesPath = adaptPath("src/test/resources/issue4427");
    ReflectionTypeSolver rts = new ReflectionTypeSolver();
    JavaParserTypeSolver jpts = new JavaParserTypeSolver(issueResourcesPath);
    CombinedTypeSolver cts = new CombinedTypeSolver();
    cts.add(rts);
    cts.add(jpts);
    ParserConfiguration pc = new ParserConfiguration()
        .setSymbolResolver(new JavaSymbolSolver(cts));
    StaticJavaParser.setConfiguration(pc);
    CompilationUnit cu = StaticJavaParser.parse(issueResourcesPath.resolve("DerivedClass.java"));

    // We shouldn't throw a mismatched symbol
    assertDoesNotThrow(() -> cu.findAll(NameExpr.class).stream()
            .map(NameExpr::resolve)
            .findAny().get());
  }
}
