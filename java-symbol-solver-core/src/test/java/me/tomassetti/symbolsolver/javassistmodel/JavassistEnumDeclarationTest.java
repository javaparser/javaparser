package me.tomassetti.symbolsolver.javassistmodel;

import me.tomassetti.symbolsolver.AbstractTest;
import me.tomassetti.symbolsolver.model.declarations.EnumDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JarTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;

public class JavassistEnumDeclarationTest extends AbstractTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() throws IOException {
        String pathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new JreTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    public void testIsInterface() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    public void testIsEnum() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isTypeVariable());
    }

    @Test
    public void testIsType() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    public void testAsType() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsClass() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asClass();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asInterface();
    }

    @Test
    public void testAsEnum() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    public void testGetQualifiedName() {
        EnumDeclaration modifier = (EnumDeclaration)typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast.Modifier", modifier.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

}
