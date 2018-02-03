package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import java.io.File;
import java.io.FileNotFoundException;

import org.junit.Test;

import static org.junit.Assert.assertNotNull;


public class Issue185 extends AbstractResolutionTest {

    @Test
    public void testIssue() throws FileNotFoundException {
        File src = adaptPath(new File("src/test/resources/recursion-issue"));
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new ReflectionTypeSolver());
        CompilationUnit agendaCu = JavaParser.parse(adaptPath(new File("src/test/resources/recursion-issue/Usage.java")));
        MethodCallExpr foo = Navigator.findMethodCall(agendaCu, "foo").get();
        assertNotNull(foo);
        JavaParserFacade.get(combinedTypeSolver).getType(foo);
    }

}
