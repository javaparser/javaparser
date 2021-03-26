package com.github.javaparser.symbolsolver;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Path;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistClassDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;

/**
 * @author 谦扬
 * @date 2019-10-25
 */
public class PullRequest2398Test extends AbstractSymbolResolutionTest {
    private TypeSolver typeSolver;

    @Test
    void onlyInlucdeJarA() throws IOException {
        Path jarAPath = adaptPath("src/test/resources/pullRequest2398/A.jar");
        typeSolver = new CombinedTypeSolver(
            new JarTypeSolver(jarAPath),
            new ReflectionTypeSolver()
        );

        JavassistClassDeclaration classDecl = (JavassistClassDeclaration)typeSolver.solveType("A");
        JavassistMethodDeclaration method = findMethodWithName(classDecl, "b");
        try {
            method.getReturnType();
            throw new RuntimeException("should throw UnsolvedSymbolException");
        } catch (Exception e) {
            assert e instanceof UnsolvedSymbolException;
        }
    }

    @Test
    void includeJarAAndB() throws IOException {
        Path jarAPath = adaptPath("src/test/resources/pullRequest2398/A.jar");
        Path jarBPath = adaptPath("src/test/resources/pullRequest2398/B.jar");
        typeSolver = new CombinedTypeSolver(
            new JarTypeSolver(jarAPath),
            new JarTypeSolver(jarBPath),
            new ReflectionTypeSolver()
        );

        JavassistClassDeclaration classDecl = (JavassistClassDeclaration)typeSolver.solveType("A");
        JavassistMethodDeclaration method = findMethodWithName(classDecl, "b");
        final ResolvedType returnType = method.getReturnType();
        assertThat(returnType.describe(), is("B"));
    }

    private JavassistMethodDeclaration findMethodWithName(JavassistClassDeclaration classDecl, String name) {
        return classDecl.getDeclaredMethods().stream().filter(methodDecl -> methodDecl.getName().equals(name))
            .map(m -> (JavassistMethodDeclaration)m).findAny().get();
    }
}
