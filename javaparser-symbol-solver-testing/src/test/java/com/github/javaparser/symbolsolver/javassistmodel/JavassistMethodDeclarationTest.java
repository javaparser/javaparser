package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;

public class JavassistMethodDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javassistmethoddecl/javassistmethoddecl.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());
    }

    @Test
    void getParameterDeclaration_forMethodParameterWithRawType() {
        JavassistClassDeclaration classDecl = (JavassistClassDeclaration) typeSolver.solveType("C");
        ResolvedMethodDeclaration methodWithRawParameter = findMethodWithNAme(classDecl, "methodWithRawParameter");

        ResolvedParameterDeclaration rawParam = methodWithRawParameter.getParam(0);

        assertThat(rawParam.describeType(), is("java.util.List"));
    }

    @Test
    void getParameterDeclaration_forMethodParameterWithGenericType() {
        JavassistClassDeclaration classDecl = (JavassistClassDeclaration) typeSolver.solveType("C");
        ResolvedMethodDeclaration methodWithRawParameter = findMethodWithNAme(classDecl, "methodWithGenericParameter");

        ResolvedParameterDeclaration genericParam = methodWithRawParameter.getParam(0);

        assertThat(genericParam.describeType(), is("java.util.List<java.lang.String>"));
    }

    private ResolvedMethodDeclaration findMethodWithNAme(JavassistClassDeclaration classDecl, String name) {
        return classDecl.getDeclaredMethods().stream().filter(methodDecl -> methodDecl.getName().equals(name)).findAny().get();
    }
}
