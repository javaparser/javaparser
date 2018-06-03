package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class JavaParserTypeSolverTest {
    @Rule
    public TemporaryFolder temporaryFolder = new TemporaryFolder();

    @Test
    public void containsLocationInStorage() {
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(CodeGenerationUtils.mavenModuleRoot(JavaParserTypeSolver.class).resolve("src/main/java"));

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver");

        JavaParserClassDeclaration declaration = (JavaParserClassDeclaration) x.getCorrespondingDeclaration();
        Node wrappedNode = declaration.getWrappedNode();
        assertEquals("JavaParserTypeSolver.java", wrappedNode.findCompilationUnit().get().getStorage().get().getFileName());
    }

    @Test
    public void folderTraversalDoesNotKeepFolderHandlesHostage() throws IOException {
        File folder = new File(temporaryFolder.getRoot(), "folder");
        assertTrue(folder.mkdirs());
        File testJava = new File(folder, "Test.java");
        assertTrue(testJava.createNewFile());
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(folder.getParentFile());
        typeSolver.tryToSolveType("folder.Test");
        assertTrue(testJava.delete());
        assertTrue(folder.delete());
        assertTrue(folder.getParentFile().delete());
    }
}
