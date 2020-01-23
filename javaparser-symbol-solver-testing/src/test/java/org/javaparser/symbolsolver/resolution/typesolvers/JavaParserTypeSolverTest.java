/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.resolution.typesolvers;

import org.javaparser.ast.Node;
import org.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import org.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.javaparser.utils.CodeGenerationUtils;
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

        SymbolReference<ResolvedReferenceTypeDeclaration> x = typeSolver.tryToSolveType("org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver");

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
