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

package com.github.javaparser.javadoc;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;

class JavadocExtractorTest {

    private int errorCount;

    @BeforeEach
    void setUp() {
        errorCount = 0;
    }

    @Test
    void canParseAllJavadocsInJavaParser() throws FileNotFoundException {
        System.err.println("About to deliberately parse a directory of files where some files have unsupported text encodings - ignore encoding-related errors that appear within the console.");
        processDir(new File(".."));
        assertEquals(2, errorCount, " ");
    }

    private void processFile(File file) throws FileNotFoundException {
        try {
            // Using (minimum) of Java 9 to avoid errors relating to parsing module-info.java files.
            StaticJavaParser.getConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_9);
            CompilationUnit cu = StaticJavaParser.parse(file);
            new VoidVisitorAdapter<Object>() {
                @Override
                public void visit(JavadocComment n, Object arg) {
                    super.visit(n, arg);
                    // FIXME: The parse problems should probably be caught/examined here, where they would specifically be about parsing javadoc rather than parsing the file itself.
                    n.parse();
                }
            }.visit(cu, null);
        } catch (ParseProblemException e) {
            System.err.println("ERROR PROCESSING "+ file);
            errorCount++;
        }
    }

    private void processDir(File dir) throws FileNotFoundException {
        for (File child : dir.listFiles()) {
            if (child.isFile() && child.getName().endsWith(".java")) {
                processFile(child);
            } else if (child.isDirectory()) {
                processDir(child);
            }
        }
    }
}
