package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistInterfaceDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.*;

public class SymbolSolverWithJavassistInterfaceTest extends AbstractTest {
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private JavassistInterfaceDeclaration interfaceDeclarationStandalone;
    private JavassistInterfaceDeclaration interfaceDeclarationSubInterfaceOwnJar;
    private JavassistInterfaceDeclaration interfaceDeclarationSubInterfaceIncludedJar;
    private JavassistInterfaceDeclaration interfaceDeclarationSubInterfaceExcludedJar;

    @Before
    public void setup() throws IOException {
        final String pathToMainJar = adaptPath("src/test/resources/javassist_symbols/main_jar/main_jar.jar");
        final String pathToIncludedJar = adaptPath("src/test/resources/javassist_symbols/included_jar/included_jar.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToIncludedJar), new JarTypeSolver(pathToMainJar), new ReflectionTypeSolver());

        symbolSolver = new SymbolSolver(typeSolver);

        interfaceDeclarationStandalone = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.StandaloneInterface");
        interfaceDeclarationSubInterfaceOwnJar = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubInterfaceOwnJar");
        interfaceDeclarationSubInterfaceIncludedJar = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubInterfaceIncludedJar");
        interfaceDeclarationSubInterfaceExcludedJar = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubInterfaceExcludedJar");
    }

    @Test
    public void testSolveSymbolInTypeCanResolveFirstNormalField() {
        assertCanSolveSymbol("STATIC_STRING", interfaceDeclarationStandalone);
    }

    @Test
    public void testSolveSymbolInTypeCanResolveSecondNormalField() {
        assertCanSolveSymbol("SECOND_STRING", interfaceDeclarationStandalone);
    }

    @Test
    public void testSolveSymbolInTypeCantResolveNonExistentField() {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = symbolSolver.solveSymbolInType(interfaceDeclarationStandalone, "FIELD_THAT_DOES_NOT_EXIST");

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
    public void testSolveSymbolInTypeCanResolveFieldInExtendedInterfaceOwnJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", interfaceDeclarationSubInterfaceOwnJar);
    }

    @Test
    public void testSolveSymbolInTypeCanResolveFieldInExtendedInterfaceIncludedJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", interfaceDeclarationSubInterfaceIncludedJar);
    }

    @Test
    public void testSolveSymbolInTypeThrowsExceptionOnResolveFieldInExtendedInterfaceExcludedJar() {
        try {
            symbolSolver.solveSymbolInType(interfaceDeclarationSubInterfaceExcludedJar, "INTERFACE_FIELD");
        } catch (Exception e) {
            assertTrue(e instanceof UnsolvedSymbolException);
            assertEquals("Unsolved symbol : com.github.javaparser.javasymbolsolver.javassist_symbols.excluded_jar.InterfaceExcludedJar", e.getMessage());
            return;
        }
        fail("Excepted NotFoundException wrapped in a RuntimeException, but got no exception.");
    }

    private void assertCanSolveSymbol(String symbolName, JavassistInterfaceDeclaration interfaceDeclaration) {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = symbolSolver.solveSymbolInType(interfaceDeclaration, symbolName);

        assertTrue(solvedSymbol.isSolved());
        assertEquals(symbolName, solvedSymbol.getCorrespondingDeclaration().asField().getName());
    }

}
