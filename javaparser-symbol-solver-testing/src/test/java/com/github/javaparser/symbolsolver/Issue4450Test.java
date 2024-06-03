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
import static org.junit.jupiter.api.Assertions.assertThrows;

public class Issue4450Test extends AbstractSymbolResolutionTest {
  @Test
  public void testIssue4450() throws IOException {
    Path issueResourcesPath = adaptPath("src/test/resources/issue4450");
    ReflectionTypeSolver rts = new ReflectionTypeSolver();
    JavaParserTypeSolver jpts = new JavaParserTypeSolver(issueResourcesPath);
    CombinedTypeSolver cts = new CombinedTypeSolver();
    cts.add(rts);
    cts.add(jpts);
    ParserConfiguration pc = new ParserConfiguration()
        .setSymbolResolver(new JavaSymbolSolver(cts));
    StaticJavaParser.setConfiguration(pc);

    // We shouldn't stack overflow
    CompilationUnit cu1 = StaticJavaParser.parse(issueResourcesPath.resolve("a/RefCycleClass.java"));
    assertDoesNotThrow(() -> cu1.findAll(NameExpr.class).stream()
            .map(NameExpr::resolve)
            .findAny().get());


    CompilationUnit cu2 = StaticJavaParser.parse(issueResourcesPath.resolve("a/RefCycleClassFailure.java"));
    assertThrows(Exception.class, () -> cu2.findAll(NameExpr.class).stream()
            .map(NameExpr::resolve)
            .findAny().get());
  }
}
