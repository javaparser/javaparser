package me.tomassetti.symbolsolver.resolution.typesolvers;

import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;


public class JarTypeSolverTest {

    @Test
    public void initial() throws IOException {
        String pathToJar = "src/test/resources/javaparser-core-2.1.0.jar";
        JarTypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.SourcesHelper").isSolved());
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.Token").isSolved());
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.ASTParser.JJCalls").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("com.github.javaparser.ASTParser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("com.github.javaparser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("Foo").isSolved());
    }

}
