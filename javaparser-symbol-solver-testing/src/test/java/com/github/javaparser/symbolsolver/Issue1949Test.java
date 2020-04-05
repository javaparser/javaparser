package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.FileNotFoundException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * https://github.com/javaparser/javaparser/issues/1949
 *
 * <pre>
 * Found another issue. (Sample project)
 * This one's quite simple, JSS is unable to solve a method call like this one:
 *
 * MyInterface.super.defaultMethod();
 * </pre>
 */
public class Issue1949Test extends AbstractSymbolResolutionTest {

    @Test
    public void testReflectionFirst() throws FileNotFoundException {

        // Paths to the relevant source root and class/interface
        Path dir = adaptPath("src/test/resources/issue1949");
        Path file_method = adaptPath("src/test/resources/issue1949/main/MyClass.java");
        Path file_interface = adaptPath("src/test/resources/issue1949/main/MyInterface.java");

        // Setup typesolver
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JavaParserTypeSolver(dir));
        typeSolver.add(new ReflectionTypeSolver(false));

        // Setup JP and parse the class
        JavaParser javaParser = new JavaParser();
        javaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit source = javaParser.parse(file_method.toFile()).getResult().get();


        // Iterate through all method calls and verify that it can be resolved.
        boolean failed = false;
        for (MethodCallExpr mce : source.findAll(MethodCallExpr.class)) {
            System.out.println("Solving at " + source.getType(0).getNameAsString() + " " + mce.getBegin().get() + ": " + mce.getNameAsString());

            try {
                mce.resolve();
                System.out.println("Success!");
            } catch (Exception e) {
                System.err.println("Error :(");
                e.printStackTrace();
                failed = true;
            }

            System.out.println();
        }

        assertFalse(failed);
    }


}
