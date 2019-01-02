package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistEnumDeclaration;
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

class SymbolSolverWithJavassistEnumTest extends AbstractSymbolResolutionTest {
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private JavassistEnumDeclaration enumDeclarationConcrete;
    private JavassistEnumDeclaration enumDeclarationInterfaceUserOwnJar;
    private JavassistEnumDeclaration enumDeclarationInterfaceUserIncludedJar;
    private JavassistEnumDeclaration enumDeclarationInterfaceUserExcludedJar;

    @BeforeEach
    void setup() throws IOException {
        final Path pathToMainJar = adaptPath("src/test/resources/javassist_symbols/main_jar/main_jar.jar");
        final Path pathToIncludedJar = adaptPath("src/test/resources/javassist_symbols/included_jar/included_jar.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToIncludedJar), new JarTypeSolver(pathToMainJar), new ReflectionTypeSolver());

        symbolSolver = new SymbolSolver(typeSolver);

        enumDeclarationConcrete = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.ConcreteEnum");
        enumDeclarationInterfaceUserOwnJar = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.EnumInterfaceUserOwnJar");
        enumDeclarationInterfaceUserIncludedJar = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.EnumInterfaceUserIncludedJar");
        enumDeclarationInterfaceUserExcludedJar = (JavassistEnumDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.EnumInterfaceUserExcludedJar");
    }

    @Test
    void testSolveSymbolInTypeCanResolveFirstEnumValue() {
        assertCanSolveSymbol("ENUM_VAL_ONE", enumDeclarationConcrete);
    }

    @Test
    void testSolveSymbolInTypeCanResolveSecondEnumValue() {
        assertCanSolveSymbol("ENUM_VAL_TWO", enumDeclarationConcrete);
    }

    @Test
    void testSolveSymbolInTypeCanResolveFirstNormalField() {
        assertCanSolveSymbol("STATIC_STRING", enumDeclarationConcrete);
    }

    @Test
    void testSolveSymbolInTypeCanResolveSecondNormalField() {
        assertCanSolveSymbol("SECOND_STRING", enumDeclarationConcrete);
    }

    @Test
    void testSolveSymbolInTypeCantResolveNonExistentField() {
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
    void testSolveSymbolInTypeCanResolveFieldInInterface() {
        assertCanSolveSymbol("INTERFACE_FIELD", enumDeclarationInterfaceUserOwnJar);
    }

    @Test
    void testSolveSymbolInTypeCanResolveFieldInInterfaceIncludedJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", enumDeclarationInterfaceUserIncludedJar);
    }

    @Test
    void testSolveSymbolInTypeThrowsExceptionOnResolveFieldInInterfaceExcludedJar() {
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
