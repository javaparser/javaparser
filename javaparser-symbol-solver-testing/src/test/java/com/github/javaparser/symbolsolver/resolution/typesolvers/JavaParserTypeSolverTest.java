package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junitpioneer.jupiter.TempDirectory;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserTypeSolverTest {

    @Disabled
    @Test
    void containsLocationInStorage() {
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(CodeGenerationUtils.mavenModuleRoot(JavaParserTypeSolver.class).resolve("src/main/java"), new LeanParserConfiguration());

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver");

        JavaParserClassDeclaration declaration = (JavaParserClassDeclaration) x.getCorrespondingDeclaration();
        Node wrappedNode = declaration.getWrappedNode();
        assertEquals("JavaParserTypeSolver.java", wrappedNode.findCompilationUnit().get().getStorage().get().getFileName());
    }

    @Test
    @ExtendWith(TempDirectory.class)
    void folderTraversalDoesNotKeepFolderHandlesHostage(@TempDirectory.TempDir Path tempDir) throws IOException {
        File folder = tempDir.resolve("folder").toFile();
        assertTrue(folder.mkdirs());
        File testJava = new File(folder, "Test.java");
        assertTrue(testJava.createNewFile());
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(folder.getParentFile());
        typeSolver.tryToSolveType("folder.Test");
    }
}
