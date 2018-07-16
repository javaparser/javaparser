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
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import static org.junit.Assert.assertEquals;

public class Issue1485 {

    @Test
    public void issue1485withoutSpecifyingJARs() throws IOException {
        File dir = new File("src/test/resources/issue1485");
        File file = new File("src/test/resources/issue1485/Complex.java");

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JavaParserTypeSolver(dir));

        JavaParser javaParser = new JavaParser();
        javaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit unit = javaParser.parse(ParseStart.COMPILATION_UNIT, new StreamProvider(new FileInputStream(file))).getResult().get();

        MethodCallExpr methodCallExpr = unit.findFirst(MethodCallExpr.class, m -> m.getName().getIdentifier().equals("println")).get();
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodCallExpr.resolve();
        assertEquals("java.io.PrintStream.println(double)", resolvedMethodDeclaration.getQualifiedSignature());
    }
}