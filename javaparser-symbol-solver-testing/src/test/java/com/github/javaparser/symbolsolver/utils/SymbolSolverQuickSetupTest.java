package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.utils.SourceRoot;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;


/**
 * Try to resolve all the ClassOrInterfaceDeclaration and MethodCallExpr in some resources folder. If it fails to do
 * so, an IllegalStateException is thrown.
 */
public class SymbolSolverQuickSetupTest {

    private Path root = Paths.get("src/test/resources/symbolsolver_quicksetup");
    private ParserConfiguration parserConfiguration = new ParserConfiguration();

    @Before
    public void setUp() throws IOException {
        SymbolSolverQuickSetup ssr = new SymbolSolverQuickSetup(root);
        TypeSolver typeSolver = ssr.walk();

        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @Test(expected = IllegalStateException.class)
    public void notResolve() throws IOException {
        SourceRoot sourceRoot = new SourceRoot(root);
        sourceRoot.tryToParse();
        // try to resolve, this will fail
        sourceRoot.getCompilationUnits().forEach(compilationUnit ->
                compilationUnit.findAll(ClassOrInterfaceDeclaration.class).forEach(ClassOrInterfaceDeclaration::resolve));
    }

    @Test
    public void resolve() throws IOException {
        SourceRoot sourceRoot = new SourceRoot(root, parserConfiguration);
        sourceRoot.tryToParse();
        // try to resolve, this should succeed
        sourceRoot.getCompilationUnits().forEach(compilationUnit ->
                compilationUnit.findAll(ClassOrInterfaceDeclaration.class).forEach(ClassOrInterfaceDeclaration::resolve));
    }
}