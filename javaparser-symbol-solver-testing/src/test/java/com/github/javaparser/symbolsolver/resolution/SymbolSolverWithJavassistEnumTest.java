package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistEnumDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.*;
import static org.junit.Assert.fail;

public class SymbolSolverWithJavassistEnumTest extends AbstractTest {
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private JavassistEnumDeclaration enumDeclarationConcrete;
    private JavassistEnumDeclaration enumDeclarationInterfaceUserOwnJar;
    private JavassistEnumDeclaration enumDeclarationInterfaceUserIncludedJar;
    private JavassistEnumDeclaration enumDeclarationInterfaceUserExcludedJar;

    @Before
    public void setup() throws IOException {
        final String pathToMainJar = adaptPath("src/test/resources/javassist_symbols/main_jar/main_jar.jar");
        final String pathToIncludedJar = adaptPath("src/test/resources/javassist_symbols/included_jar/included_jar.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToIncludedJar), new JarTypeSolver(pathToMainJar), new ReflectionTypeSolver());

        symbolSolver = new SymbolSolver(typeSolver);

        enumDeclarationConcrete = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.ConcreteEnum");
        enumDeclarationInterfaceUserOwnJar = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.EnumInterfaceUserOwnJar");
        enumDeclarationInterfaceUserIncludedJar = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.EnumInterfaceUserIncludedJar");
        enumDeclarationInterfaceUserExcludedJar = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.EnumInterfaceUserExcludedJar");
    }

    @Test
    public void testSolveSymbolInTypeCanResolveFirstEnumValue() {
        assertCanSolveSymbol("ENUM_VAL_ONE", enumDeclarationConcrete);
    }

    @Test
    public void testSolveSymbolInTypeCanResolveSecondEnumValue() {
        assertCanSolveSymbol("ENUM_VAL_TWO", enumDeclarationConcrete);
    }

    @Test
    public void testSolveSymbolInTypeCanResolveFirstNormalField() {
        assertCanSolveSymbol("STATIC_STRING", enumDeclarationConcrete);
    }

    @Test
    public void testSolveSymbolInTypeCanResolveSecondNormalField() {
        assertCanSolveSymbol("SECOND_STRING", enumDeclarationConcrete);
    }

    @Test
    public void testSolveSymbolInTypeCantResolveNonExistentField() {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = symbolSolver.solveSymbolInType(enumDeclarationConcrete, "FIELD_THAT_DOES_NOT_EXIST");

        assertFalse(solvedSymbol.isSolved());

        try {
            solvedSymbol.getCorrespondingDeclaration();
        } catch (Exception e) {
            assertTrue(e instanceof UnsupportedOperationException);
            assertEquals("CorrespondingDeclaration not available for unsolved symbol.", e.getMessage());
            return;
        }
        fail("Expected UnsupportedOperationException when requesting CorrespondingDeclaration on unsolved SymbolRefernce");
    }

    @Test
    public void testSolveSymbolInTypeCanResolveFieldInInterface() {
        assertCanSolveSymbol("INTERFACE_FIELD", enumDeclarationInterfaceUserOwnJar);
    }

    @Test
    public void testSolveSymbolInTypeCanResolveFieldInInterfaceIncludedJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", enumDeclarationInterfaceUserIncludedJar);
    }

    @Test
    public void testSolveSymbolInTypeThrowsExceptionOnResolveFieldInInterfaceExcludedJar() {
        try {
            symbolSolver.solveSymbolInType(enumDeclarationInterfaceUserExcludedJar, "INTERFACE_FIELD");
        } catch (Exception e) {
            assertTrue(e instanceof UnsolvedSymbolException);
            assertEquals("Unsolved symbol : com.github.javaparser.javasymbolsolver.javassist_symbols.excluded_jar.InterfaceExcludedJar", e.getMessage());
            return;
        }
        fail("Excepted NotFoundException wrapped in a RuntimeException, but got no exception.");
    }

    private void assertCanSolveSymbol(String symbolName, JavassistEnumDeclaration enumDeclaration) {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = symbolSolver.solveSymbolInType(enumDeclaration, symbolName);

        assertTrue(solvedSymbol.isSolved());
        assertEquals(symbolName, solvedSymbol.getCorrespondingDeclaration().asField().getName());
    }
}
