package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class JavaParserTypeSolverTest {
    @Test
    public void containsLocationInStorage() {
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(CodeGenerationUtils.mavenModuleRoot(JavaParserTypeSolver.class).resolve("src/main/java"));

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver");

        JavaParserClassDeclaration declaration = (JavaParserClassDeclaration) x.getCorrespondingDeclaration();
        Node wrappedNode = declaration.getWrappedNode();
        assertEquals("JavaParserTypeSolver.java", wrappedNode.findCompilationUnit().get().getStorage().get().getFileName());
    }
}
