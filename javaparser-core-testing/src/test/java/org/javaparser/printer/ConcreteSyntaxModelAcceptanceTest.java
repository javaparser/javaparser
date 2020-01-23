/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package org.javaparser.printer;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.Node;
import org.javaparser.utils.CodeGenerationUtils;
import org.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ConcreteSyntaxModelAcceptanceTest {
    private final Path rootDir = CodeGenerationUtils.mavenModuleRoot(ConcreteSyntaxModelAcceptanceTest.class).resolve("src/test/test_sourcecode");

    private String prettyPrint(Node node) {
        return ConcreteSyntaxModel.genericPrettyPrint(node);
    }

    private String prettyPrintedExpectation(String name) throws IOException {
        return TestUtils.readResource("org/javaparser/printer/" + name + "_prettyprinted");
    }

    @Test
    void printingExamplePrettyPrintVisitor() throws IOException {
        CompilationUnit cu = parse(rootDir.resolve("com/github/javaparser/printer/PrettyPrintVisitor.java"));
        assertEquals(prettyPrintedExpectation("PrettyPrintVisitor"), prettyPrint(cu));
    }

    @Test
    void printingExampleJavaConcepts() throws IOException {
        CompilationUnit cu = parse(rootDir.resolve("com/github/javaparser/printer/JavaConcepts.java"));
        assertEquals(prettyPrintedExpectation("JavaConcepts"), prettyPrint(cu));
    }

}
