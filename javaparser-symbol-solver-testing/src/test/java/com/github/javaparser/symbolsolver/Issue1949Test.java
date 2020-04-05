package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

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
 *
 */
public class Issue1949Test {

    private static List<TypeSolver> getTypeSolvers() {
        List<TypeSolver> solvers = new ArrayList<>();
        solvers.add(new JavaParserTypeSolver("src/main/java"));
        solvers.add(new ReflectionTypeSolver(false));
        return solvers;
    }

    @ParameterizedTest
    @MethodSource("getTypeSolvers")
    public void testReflectionFirst(TypeSolver typeSolver) throws FileNotFoundException {
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);

        CompilationUnit source = StaticJavaParser.parse(new File("src/main/java/main/MyClass.java"));
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
