/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.concurrent.CompletableFuture;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.*;

class JavaParserTypeSolverTest extends AbstractTypeSolverTest<JavaParserTypeSolver> {

    private static final Supplier<JavaParserTypeSolver> JAVA_PARSER_PROVIDER = () -> {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        return new JavaParserTypeSolver(src);
    };

    public JavaParserTypeSolverTest() {
        super(JAVA_PARSER_PROVIDER);
    }

    @Disabled // Unsure why this test is disabled -- passes locally.
    @Test
    void containsLocationInStorage() {
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(
                CodeGenerationUtils.mavenModuleRoot(JavaParserTypeSolver.class).resolve("src/main/java"),
                new LeanParserConfiguration()
        );

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver");

        JavaParserClassDeclaration declaration = (JavaParserClassDeclaration) x.getCorrespondingDeclaration();
        Node wrappedNode = declaration.getWrappedNode();
        assertEquals("JavaParserTypeSolver.java", wrappedNode.findCompilationUnit().get().getStorage().get().getFileName());
    }

    @Test
    void folderTraversalDoesNotKeepFolderHandlesHostage(@TempDir Path tempDir) throws IOException {
        File folder = tempDir.resolve("folder").toFile();
        assertTrue(folder.mkdirs());

        File testJava = new File(folder, "Test.java");
        assertTrue(testJava.createNewFile());

        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(folder.getParentFile());
        typeSolver.tryToSolveType("folder.Test");
    }


    @Test
    public void givenJavaParserTypeSolver_tryToSolveClass_expectSuccess() {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit");

        assertTrue(x.isSolved());
        assertNotNull(x.getCorrespondingDeclaration());
        assertTrue(x.getCorrespondingDeclaration().isClass());
    }

    @Test
    public void givenJavaParserTypeSolver_tryToSolveClassWithGeneric_expectSuccess() {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.ParseResult");

        assertTrue(x.isSolved());
        assertNotNull(x.getCorrespondingDeclaration());
        assertTrue(x.getCorrespondingDeclaration().isClass());
    }

    @Test
    public void givenJavaParserTypeSolver_tryToSolveEnum_expectSuccess() {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.ast.Modifier");

        assertTrue(x.isSolved());
        assertNotNull(x.getCorrespondingDeclaration());
        assertTrue(x.getCorrespondingDeclaration().isEnum());
    }

    @Test
    public void givenJavaParserTypeSolver_tryToSolveInterface_expectSuccess() {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration");

        assertTrue(x.isSolved());
        assertNotNull(x.getCorrespondingDeclaration());
        assertTrue(x.getCorrespondingDeclaration().isInterface());
    }

    @Test
    public void givenJavaParserTypeSolver_tryToSolveInterfaceWithGeneric_expectSuccess() {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("com.github.javaparser.ast.nodeTypes.NodeWithName");

        assertTrue(x.isSolved());
        assertNotNull(x.getCorrespondingDeclaration());
        assertTrue(x.getCorrespondingDeclaration().isInterface());
    }
    
    @Test
    public void givenJavaParserTypeSolver_tryToSolveAnUnexpectedSourceFileName_expectSuccess() {
        Path src = adaptPath("src/test/test_sourcecode");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("A<>");

        assertFalse(x.isSolved());
    }

    /**
     * {@link com.github.javaparser.JavaParser} doesn't work across multiple threads.
     *
     * This test makes sure the concurrency is handled.
     */
    @RepeatedTest(25)
    void testTryToSolveTypeWithMultipleThreads() {
        class StressRunnable implements Runnable {

            private final String typeToSolve;
            private final JavaParserTypeSolver javaParserTypeSolver;

            StressRunnable(String typeToSolve, JavaParserTypeSolver javaParserTypeSolver) {
                this.typeToSolve = typeToSolve;
                this.javaParserTypeSolver = javaParserTypeSolver;
            }

            @Override
            public void run() {
                javaParserTypeSolver.tryToSolveType(typeToSolve);
            }
        }

        JavaParserTypeSolver javaParserTypeSolver = JAVA_PARSER_PROVIDER.get();

        CompletableFuture<Void> tasks = CompletableFuture.allOf(
                CompletableFuture.runAsync(new StressRunnable("com.github.javaparser.ast.body.Object",
                        javaParserTypeSolver)),
                CompletableFuture.runAsync(new StressRunnable("com.github.javaparser.ast.comments.Object",
                        javaParserTypeSolver)),
                CompletableFuture.runAsync(new StressRunnable("com.github.javaparser.ast.expr.Object",
                        javaParserTypeSolver)),
                CompletableFuture.runAsync(new StressRunnable("com.github.javaparser.ast.stmt.Object",
                        javaParserTypeSolver))
        );
        assertDoesNotThrow(tasks::join,
                "JavaParserTypeSolve should work properly when called from multiple threads.");
    }

}
