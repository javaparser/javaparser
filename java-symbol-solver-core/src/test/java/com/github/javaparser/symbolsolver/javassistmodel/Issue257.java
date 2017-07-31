package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

public class Issue257 extends AbstractTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() throws IOException {
        String pathToJar = adaptPath("src/test/resources/issue257/issue257.jar");
        File jar = new File(pathToJar);
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(jar.getAbsolutePath()), new ReflectionTypeSolver());
    }

    @Test
    public void verifyBCanBeSolved() throws FileNotFoundException {
        typeSolver.solveType("net.testbug.B");
    }

    @Test
    public void issue257() throws FileNotFoundException {
        String pathToSourceFile = adaptPath("src/test/resources/issue257/A.java.txt");
        CompilationUnit cu = JavaParser.parse(new File(pathToSourceFile));
        Statement statement = cu.getClassByName("A").get().getMethodsByName("run").get(0).getBody().get().getStatement(0);
        ExpressionStmt expressionStmt = (ExpressionStmt)statement;
        Expression expression = expressionStmt.getExpression();
        JavaParserFacade.get(typeSolver).getType(expression);
    }

}
