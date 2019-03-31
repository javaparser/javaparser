package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue1485Test extends AbstractSymbolResolutionTest {

    @Test
    void issue1485withoutSpecifyingJARs() throws IOException {
        Path dir = adaptPath("src/test/resources/issue1485");
        Path file = adaptPath("src/test/resources/issue1485/Complex.java");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(dir, new LeanParserConfiguration()));

        JavaParser javaParser = new JavaParser();
        javaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT,
                new StreamProvider(Files.newInputStream(file))).getResult().get();

        MethodCallExpr methodCallExpr = unit.findFirst(MethodCallExpr.class, m -> m.getName().getIdentifier().equals("println")).get();
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodCallExpr.resolve();
        assertEquals("java.io.PrintStream.println(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }
}