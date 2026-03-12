package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.FileNotFoundException;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/8/26)
 */
public class Issue4969Test {
    @Test
    void preferVisibleMethods() throws FileNotFoundException {
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(new ReflectionTypeSolver());
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(symbolSolver);
        JavaParser javaParser = new JavaParser(config);

        CompilationUnit cu = javaParser.parse(new File("src/test/resources/issue4969/A.java")).getResult().get();
        MethodCallExpr expr = cu.findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration decl = expr.resolve();

        assertEquals("A.m(long)", decl.getQualifiedSignature());
    }
}
