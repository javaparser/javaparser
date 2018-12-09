/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.apache.commons.io.Charsets;
import org.junit.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.charset.StandardCharsets;

public class JavadocExtractorTest {

    @Test
    public void canParseAllJavadocsInJavaParser() throws FileNotFoundException {
        processDir(new File(".."));
    }

    private void processFile(File file) throws FileNotFoundException {
        try {
            CompilationUnit cu = JavaParser.parse(file, StandardCharsets.UTF_8);
            new VoidVisitorAdapter<Object>() {
                @Override
                public void visit(JavadocComment n, Object arg) {
                    super.visit(n, arg);
                    n.parse();
                }
            }.visit(cu, null);
        } catch (ParseProblemException e) {
            System.err.println("ERROR PROCESSING "+ file);
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
