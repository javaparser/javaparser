package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistInterfaceDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class SymbolSolverWithJavassistInterfaceTest extends AbstractSymbolResolutionTest {
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private JavassistInterfaceDeclaration interfaceDeclarationStandalone;
    private JavassistInterfaceDeclaration interfaceDeclarationSubInterfaceOwnJar;
    private JavassistInterfaceDeclaration interfaceDeclarationSubInterfaceIncludedJar;
    private JavassistInterfaceDeclaration interfaceDeclarationSubInterfaceExcludedJar;

    @BeforeEach
    void setup() throws IOException {
        final Path pathToMainJar = adaptPath("src/test/resources/javassist_symbols/main_jar/main_jar.jar");
        final Path pathToIncludedJar = adaptPath("src/test/resources/javassist_symbols/included_jar/included_jar.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToIncludedJar), new JarTypeSolver(pathToMainJar), new ReflectionTypeSolver());

        symbolSolver = new SymbolSolver(typeSolver);

        interfaceDeclarationStandalone = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.StandaloneInterface");
        interfaceDeclarationSubInterfaceOwnJar = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubInterfaceOwnJar");
        interfaceDeclarationSubInterfaceIncludedJar = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubInterfaceIncludedJar");
        interfaceDeclarationSubInterfaceExcludedJar = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubInterfaceExcludedJar");
    }

    @Test
    void testSolveSymbolInTypeCanResolveFirstNormalField() {
        assertCanSolveSymbol("STATIC_STRING", interfaceDeclarationStandalone);
    }

    @Test
    void testSolveSymbolInTypeCanResolveSecondNormalField() {
        assertCanSolveSymbol("SECOND_STRING", interfaceDeclarationStandalone);
    }

    @Test
    void testSolveSymbolInTypeCantResolveNonExistentField() {
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
    void testSolveSymbolInTypeCanResolveFieldInExtendedInterfaceOwnJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", interfaceDeclarationSubInterfaceOwnJar);
    }

    @Test
    void testSolveSymbolInTypeCanResolveFieldInExtendedInterfaceIncludedJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", interfaceDeclarationSubInterfaceIncludedJar);
    }

    @Test
    void testSolveSymbolInTypeThrowsExceptionOnResolveFieldInExtendedInterfaceExcludedJar() {
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
