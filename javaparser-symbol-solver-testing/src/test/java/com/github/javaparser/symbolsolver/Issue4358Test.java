package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

public class Issue4358Test extends AbstractSymbolResolutionTest {
  @Test
  public void testIssue4358() throws IOException {
    Path issueResourcesPath = adaptPath("src/test/resources/issue4358");
    ReflectionTypeSolver rts = new ReflectionTypeSolver();
    JavaParserTypeSolver jpts = new JavaParserTypeSolver(issueResourcesPath);
    CombinedTypeSolver cts = new CombinedTypeSolver();
    cts.add(rts);
    cts.add(jpts);
    ParserConfiguration pc = new ParserConfiguration()
        .setSymbolResolver(new JavaSymbolSolver(cts));
    StaticJavaParser.setConfiguration(pc);
    CompilationUnit cu = StaticJavaParser.parse(issueResourcesPath.resolve("foo/A.java"));

    // There's only one method call in this compilation unit
    ResolvedMethodDeclaration actual = cu.findAll(MethodCallExpr.class).stream()
        .map(MethodCallExpr::resolve)
        .findAny().get();

    assertEquals("foo.B.d()", actual.getQualifiedSignature());
  }
}
